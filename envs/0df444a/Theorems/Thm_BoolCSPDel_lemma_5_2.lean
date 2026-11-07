-- Prove2me | Theorems.Thm_BoolCSPDel_lemma_5_2
-- name    : BoolCSPDel.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:18.476208+00:00
-- url     : https://prove2.me/theorems/eddfa3e6-d2aa-4480-8ffe-fec8f6f89162
-- title:
--   Lemma 5.2 — polynomial representation: energy is $0$ on solutions and at least $1$ off them
-- statement:
--   Let $\Gamma$ be a nonempty language of nonempty proper relations and $d=\deg_{\mathbb Z}(\Gamma)$. With $D$ the number of sets $T\subseteq[n]$, $|T|\le d$, we have $n+1\le D\le C(n+1)^d$, and there is an integer matrix $B$ with rows indexed by constraints and columns by these sets such that $b_C^\top\phi(\alpha)=0$ exactly when $\alpha$ satisfies $C$. For $f\ge0$ and $G_f=B^\top\mathrm{diag}(f)^2B$, every assignment $\alpha$ satisfies
--
--   $$\phi(\alpha)^\top G_f\phi(\alpha)\begin{cases}=0,&\alpha\in\mathrm{Sat}_\Gamma(f),\\\ge1,&\alpha\notin\mathrm{Sat}_\Gamma(f).\end{cases}$$
--
--   Each row has $O_k(1)$ nonzero entries and squared norm $O_k(1)$, and one program, independent of $n$, writes it from $n$ and the constraint in polynomial time and $O_k(\log(n+2))$ cells.
--
--   The gap between $0$ and $1$ is what lets an approximate matrix preserve the solutions exactly.
--
--   Differences from the source:
--   - generalization: one relation R of arity k → a finite language Γ of relations of arity at most k; reason: the paper states this form on the cited page and uses it; Γ = {R} is the printed case
--   - reading: D = O_k(n^d), for every n → D ≤ C (n + 1)^d; reason: at n = 0 the formula on p.30 gives D = 1 while n^d = 0; for n ≥ 1 the two forms are the same up to the constant
--   - generalization: ∃ D, a map ϕ of monomial values, B → D, ϕ the monomial coordinates of the proof, and the property b_Cᵀϕ(α) = 0 ⇔ α satisfies C as a conjunct; reason: the proof prints them (pp.30–31) and Corollary 5.10 uses them
--   - reading: each row "can be generated from its scope in polynomial time and O_k(log(n + 2)) workspace", no machine named → one coin-free Program for all n that, on encNat n ++ conBlock of the constraint, halts with the row word at cell 0 within (n + 2)^c steps and C log(n + 2) cells; reason: the machine of the upper bound (p.17 counts all retained memory); the cells include the output, which has O_k(log(n + 2)) bits
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Lemma 5.2, p.30; proof of Corollary 5.10, p.37

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_dictOracle

namespace BoolCSPDel

/-- **Lemma 5.2 (polynomial representation), language form.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Lemma 5.2, p.30, and the proof of
Corollary 5.10, p.37.

With `D` the number of monomial coordinates `T ⊆ [n]`, `|T| ≤ d`, and `ϕ` the monomial values: `n + 1 ≤ D`
and `D = O_k(n^d)`; there are an integer matrix `B` whose rows represent the constraints, and for
`G = Bᵀdiag(f)²B`, `f ≥ 0`, the energy `ϕ(α)ᵀGϕ(α)` is `0` on `Sat(f)` and at least `1` off it. Each row has
`O_k(1)` nonzero entries and squared norm `O_k(1)`, and one coin-free program writes it from `n` and the
scope in polynomial time and `O_k(log(n + 2))` cells.

**Formalization Note.** `D = O_k(n^d)` is stated as `D ≤ C (n + 1)^d`, as at `n = 0` the coordinates still
contain the constant monomial. The row word lists the nonzero coordinates. The representation property
`IsPolyRep` is printed in the proof (p.31) and is what Corollary 5.10 uses. -/
theorem lemma_5_2 (k : ℕ) : ∃ C c : ℕ, ∀ Γ : Lang k, Γ.Nonempty → AllNonemptyProper Γ →
    ∃ (B : ∀ n : ℕ, Matrix (Con Γ (Fin n)) (Mono n (degZLang Γ)) ℤ) (Pg : Program), OracleFree Pg ∧
      ∀ n : ℕ,
        n + 1 ≤ Fintype.card (Mono n (degZLang Γ)) ∧
        Fintype.card (Mono n (degZLang Γ)) ≤ C * (n + 1) ^ degZLang Γ ∧
        IsPolyRep (B n) ∧
        (∀ (f : Con Γ (Fin n) → ℤ), (∀ U, 0 ≤ f U) → ∀ α : Fin n → Bool,
          (α ∈ Sat f → phi α ⬝ᵥ ((gramR (B n) f).mulVec (phi α)) = 0) ∧
          (α ∉ Sat f → 1 ≤ phi α ⬝ᵥ ((gramR (B n) f).mulVec (phi α)))) ∧
        (∀ U : Con Γ (Fin n),
          (Finset.univ.filter fun T => B n U T ≠ 0).card ≤ C ∧ ∑ T, (B n U T) ^ 2 ≤ (C : ℤ) ∧
          ∀ coins : ℕ → Bool, ∃ cfg, HaltsWith Pg noOracle (encNat n ++ conBlock Γ n U) coins cfg ∧
            cfg.steps ≤ (n + 2) ^ c ∧ (cfg.space : ℝ) ≤ C * Real.log (n + 2) ∧
            ∃ L : List (Mono n (degZLang Γ) × ℤ), (L.map Prod.fst).Nodup ∧
              (∀ e ∈ L, e.2 ≠ 0) ∧ (∀ T, B n U T = (L.lookup T).getD 0) ∧
              TapeHolds cfg.tape 0 (monoRowWord L)) := by sorry

end BoolCSPDel
