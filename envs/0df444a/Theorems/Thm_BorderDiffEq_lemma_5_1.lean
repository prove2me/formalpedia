-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_5_1
-- name    : BorderDiffEq.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:24.45587+00:00
-- url     : https://prove2.me/theorems/3fa052bc-5991-4d66-8a3b-7515138dcafb
-- title:
--   Lemma 5.1 — the differential equation $\sum_jA_jD^jF_\varepsilon=0$ and its limit $\sum_jb_jD^jF=0$
-- statement:
--   Let $F$ be a field of characteristic zero, $k\ge1$, and let $T_1,\dots,T_k$ be nonzero polynomials in $x$ over $F((\varepsilon))$ with
--   $$
--   f_\varepsilon:=T_1+\dots+T_k=f+O(\varepsilon),\qquad f\in F[x].
--   $$
--   Let $S_i:=\Phi_y(T_i)$, $F_\varepsilon:=\Phi_y(f_\varepsilon)$, $F:=\Phi_y(f)$, $D=\partial/\partial z$. Let $S_{e(1)},\dots,S_{e(r)}$ be any maximal subfamily of $S_1,\dots,S_k$ that is linearly independent over $F((\varepsilon))(y,x)$, let $M$ be the $r\times(r+1)$ matrix with rows $(S_{e(i)},DS_{e(i)},\dots,D^rS_{e(i)})$, and $A_j:=(-1)^j\det(M_{j+1})$ for $0\le j\le r$. Then $1\le r\le k$ and:
--
--   1. $\displaystyle\sum_{j=0}^rA_j\,D^jF_\varepsilon=0$, and $A_r=(-1)^rW(S_{e(1)},\dots,S_{e(r)})\neq0$;
--   2. $A_j(y,z,x)=A_j(y+zx,0,x)$ for every $0\le j\le r$;
--   3. with $m:=\mathrm{val}_\varepsilon(A_r)$, $\mathrm{val}_\varepsilon(A_j)\ge m$ for every $j$, and $b_j:=\lim_{\varepsilon\to0}\varepsilon^{-m}A_j\in F[y,z,x]$ satisfy
--   $$
--   \sum_{j=0}^rb_j(y,z,x)\,D^jF(y,z,x)=0,\qquad b_r(y,0,x)\neq0,
--   $$
--   and $b_j(y,z,x)=b_j(y+zx,0,x)$ for every $j$.
--
--   This is the paper's central construction: a single linear differential equation in $z$, satisfied by the limit $f$ of the approximations, whose leading coefficient does not vanish at $z=0$.
--
--   **Formalization Note** $f+O(\varepsilon)$ is `IsEpsApprox`. A maximal independent subfamily is an injective $e:\{1..r\}\to\{1..k\}$ with $(S_{e(j)})_j$ independent over the coefficient ring and every $S_i$ satisfying $c\,S_i=\sum_ja_jS_{e(j)}$ with $c\ne0$; the conclusion is asserted for every such choice. $A_j$ is `signedMinor (derivMatrix …) j`, $b_j$ is `epsCoeff m (A j)`, and $(y,z)\mapsto(y+zx,0)$ is `diagSubst`.
--
--   Differences from the source:
--   - generalization: constants in $F(\varepsilon)$ → constants in $F((\varepsilon))$ (`LaurentSeries F`); reason: $F(\varepsilon)\subset F((\varepsilon))$ and $\mathrm{val}_\varepsilon$, $\lim_{\varepsilon\to0}\varepsilon^{-m}$ restrict to the paper's; the source's instances are instances of the Lean statement
--   - encoding: polynomials in $F(\varepsilon)[y,z,x]$, independence over $F(\varepsilon,y,x)$ → `Polynomial` in $z$ over `MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F)`, independence over that coefficient ring; reason: independence over a domain equals independence over its fraction field (clear denominators), and independence of vectors with coordinates in a field is unchanged by a field extension
--   - generalization: $f_\varepsilon=f+O(\varepsilon)$ for $T_i\in F(\varepsilon)[x]$ → $f_\varepsilon=f+\varepsilon S$ with $S\in F[[\varepsilon]][x]$; reason: for $T_i\in F(\varepsilon)[x]$ this is the same condition; it is stated for all $T_i$ over $F((\varepsilon))$
--   - encoding: "after renumbering, a maximal subset … linearly independent" → every injective $e$ with $S\circ e$ independent and every $S_i$ in its span over the fraction field (witnessed by $c\ne0$ and $a_j$); reason: this is maximality; quantifying over all choices states the lemma for whichever subset is taken
--   - encoding: $T_1,\dots,T_k$ with $1\le r\le k$ → hypothesis $1\le k$; reason: the source presupposes a nonempty family ($1\le r\le k$ is impossible for $k=0$); this only excludes that undefined case
--   - encoding: $m:=\mathrm{val}_\varepsilon(A_r)$, $b_j:=\lim\varepsilon^{-m}A_j$ → $\exists m\in\mathbb Z$ with $\mathrm{val}_\varepsilon(A_r)=m$, $b_j=$ `epsCoeff m (A j)`; reason: $A_r\ne0$, so its valuation is a unique integer
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 5.1, p.31

import Mathlib
import Definitions.Def_BorderDiffEq_IsEpsApprox
import Definitions.Def_BorderDiffEq_shift
import Definitions.Def_BorderDiffEq_diagSubst
import Definitions.Def_BorderDiffEq_wronskian
import Definitions.Def_BorderDiffEq_derivMatrix
import Definitions.Def_BorderDiffEq_signedMinor
import Definitions.Def_BorderDiffEq_epsVal
import Definitions.Def_BorderDiffEq_epsCoeff

namespace BorderDiffEq

/-- **Lemma 5.1 (the differential equation)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying
Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027
submission), Lemma 5.1, p.31). Let `T₁, …, T_k ∈ F(ε)[x]` be nonzero with
`f_ε := T₁ + ⋯ + T_k = f + O(ε)`, `f ∈ F[x]`. Let `Sᵢ := Φ_y(Tᵢ)`, `F_ε := Φ_y(f_ε)`,
`F := Φ_y(f)`. Let `S_{e(1)}, …, S_{e(r)}` be a maximal subfamily of `S₁, …, S_k` linearly
independent over `F(ε, y, x)`, `M` the `r × (r+1)` matrix with rows `(S, DS, …, D^r S)` and
`Aⱼ := (-1)^j det(M_{j+1})`. Then `1 ≤ r ≤ k` and:
(1) `∑ⱼ Aⱼ D^j F_ε = 0` and `A_r = (-1)^r W(S_{e(1)}, …, S_{e(r)}) ≠ 0`;
(2) `Aⱼ(y, z, x) = Aⱼ(y + z x, 0, x)` for every `j`;
(3) with `m := val_ε(A_r)`, `val_ε(Aⱼ) ≥ m` for every `j`, and `bⱼ := lim_{ε→0} ε^{-m} Aⱼ ∈ F[y, z, x]`
satisfy `∑ⱼ bⱼ D^j F = 0`, `b_r(y, 0, x) ≠ 0`, and `bⱼ(y, z, x) = bⱼ(y + z x, 0, x)`.

**Formalization Note.** `F` any field of characteristic zero; `F(ε)` generalized to `F((ε))`;
`f + O(ε)` is `IsEpsApprox`. "After renumbering, a maximal linearly independent subset" is: every
injective `e : Fin r → Fin k` such that `S ∘ e` is linearly independent over the coefficient ring
`R = MvPolynomial (Fin n ⊕ Fin n) F((ε))` and every `Sᵢ` satisfies `c • Sᵢ = ∑ⱼ aⱼ • S_{e(j)}` with
`c ≠ 0` (i.e. lies in the span over `Frac R = F((ε))(y, x)`). `Aⱼ = signedMinor (derivMatrix …) j`,
`bⱼ = epsCoeff m Aⱼ`, `D = Polynomial.derivative`, `(y, z) ↦ (y + z x, 0)` is `diagSubst`, and
`b_r(y, 0, x)` is `Polynomial.eval 0`. `1 ≤ k` is assumed (the family `T₁, …, T_k` is nonempty). -/
theorem lemma_5_1 (F : Type) [Field F] [CharZero F] (n k : ℕ) (hk : 1 ≤ k)
    (T : Fin k → MvPolynomial (Fin n) (LaurentSeries F)) (hT : ∀ i, T i ≠ 0)
    (f : MvPolynomial (Fin n) F) (hf : IsEpsApprox (∑ i, T i) f)
    (r : ℕ) (e : Fin r → Fin k) (he : Function.Injective e)
    (hind : LinearIndependent (MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F))
      (fun j => shift (T (e j))))
    (hmax : ∀ i, ∃ c : MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F), c ≠ 0 ∧
      ∃ a : Fin r → MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F),
        c • shift (T i) = ∑ j, a j • shift (T (e j))) :
    let A : Fin (r + 1) → Polynomial (MvPolynomial (Fin n ⊕ Fin n) (LaurentSeries F)) :=
      signedMinor (derivMatrix (fun j => shift (T (e j))))
    1 ≤ r ∧ r ≤ k ∧
    -- (1)
    (∑ j : Fin (r + 1), A j * Polynomial.derivative^[(j : ℕ)] (shift (∑ i, T i)) = 0 ∧
      A (Fin.last r) = (-1) ^ r * wronskian (fun j => shift (T (e j))) ∧
      wronskian (fun j => shift (T (e j))) ≠ 0) ∧
    -- (2)
    (∀ j, diagSubst (A j) = A j) ∧
    -- (3)
    (∃ m : ℤ, epsVal (A (Fin.last r)) = m ∧ (∀ j, (m : WithTop ℤ) ≤ epsVal (A j)) ∧
      ∑ j : Fin (r + 1), epsCoeff m (A j) * Polynomial.derivative^[(j : ℕ)] (shift f) = 0 ∧
      (epsCoeff m (A (Fin.last r))).eval 0 ≠ 0 ∧
      ∀ j, diagSubst (epsCoeff m (A j)) = epsCoeff m (A j)) := by sorry

end BorderDiffEq
