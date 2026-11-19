-- Prove2me | Theorems.Thm_AC02Frege_Supplement_theorem_1_5
-- name    : AC02Frege.Supplement.theorem_1_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:59:50.392023+00:00
-- url     : https://prove2.me/theorems/a36598d8-9457-4784-85ab-36e329cc7682
-- title:
--   Theorem 1.5 — $\mathrm{Res}(\mathrm{PC})$ without degree bound needs total size $\exp(\Omega((\log n)^{5/2}))$ on $G\circ\mathrm{Sel}_N$
-- statement:
--   Let $F$ be a constant-width CNF on $n$ variables with no PC refutation over $\mathbb F_2$ of degree $cn$, let $G=F\circ\mathrm{Maj}_\ell$ be its majority lift with $\ell=\Theta(\log n)$ odd, chosen as in Corollary 4.21, and let $q=N=n\ell$. Then $G\circ\mathrm{Sel}_q$ is an unsatisfiable CNF of size polynomial in $n$, and every $\mathrm{Res}(\mathrm{PC})$ refutation of it, with no bound on the degree of its polynomials, has total size
--   $$
--   T\ \ge\ \exp\bigl(\Omega((\log n)^{5/2})\bigr).
--   $$
--
--   Precisely: for every $c>0$ and $0<\lambda_1\le\lambda_2$ there is $\alpha>0$ such that for every width bound $w$ there are $k$ and $n_0$ with the following property. For every $n\ge n_0$, every unsatisfiable CNF $F$ on $n$ variables of width at most $w$ with no PC refutation of degree $\lfloor cn\rfloor$, and every odd $\ell$ with $\lambda_1\log n\le\ell\le\lambda_2\log n$:
--
--   1. $G\circ\mathrm{Sel}_{n\ell}$ is unsatisfiable;
--   2. its encoding length is at most $n^k$;
--   3. every $\mathrm{Res}(\mathrm{PC})$ refutation of it has total size $T$ with $\log T\ge\alpha(\log n)^{5/2}$.
--
--   The bound is quasipolynomial in the number of variables and superpolynomial in the size of the formula; it is the paper's lower bound for unrestricted-degree $\mathrm{Res}(\mathrm{PC})$ measured by total size.
--
--   **Formalization Note** $G$ is the base `lift F ℓ`, size is the base `encLength`, and the refutation runs over the variables $((i,a),b,a')$ of $G\circ\mathrm{Sel}_{n\ell}$.
--
--   Differences from the source:
--   - reading: F "a constant-width CNF with no PC refutation of degree cn", G = F ∘ Maj_ℓ with ℓ "chosen as in Corollary 4.21" → F also unsatisfiable (¬ Satisfiable F); reason: Corollary 4.21 is stated under the hypotheses of Theorem 4.20, which include unsatisfiability, and Definition 1.2 says F requires PC degree cn; without it the conclusion 'G ∘ Sel_q is unsatisfiable' fails for every satisfiable F
--   - generalization: ℓ = Θ(log n) "chosen as in Corollary 4.21" (a sufficiently large constant times log n, rounded up to an odd integer) → for all 0 < λ₁ ≤ λ₂, every odd ℓ with λ₁ log n ≤ ℓ ≤ λ₂ log n, quantified before ∃ α (as in the base goal, Theorem 1.4); reason: Corollary 4.21's choice ℓ = ⌈λ log n⌉_odd lies in the window [λ log n, 2λ log n] for large n, so the statement specializes to the source
--   - reading: T ≥ exp(Ω((log n)^{5/2})); F of constant width; 'of size polynomial in n' → ∃ α > 0 after c, λ₁, λ₂ and before the width bound w, with α (log n)^{5/2} ≤ log T; ∃ k n₀ after w; reason: the quantifier order of the base goal (Theorem 1.4, whose F and G Theorem 1.5 takes); the stronger reading of Ω, since the proof's constant comes from d ≍ (log n)^{3/2} and Theorem 4.20's C, which depends on c only
--   - generalization: c in (0, 1) (hypotheses of Theorem 4.20); Definition 1.2 says c > 0 → every c > 0; reason: the hypothesis 'no PC refutation of degree ⌊cn⌋' is monotone in c, so c ≥ 1 reduces to c = 1/2
--   - reading: "G ∘ Sel_q is an unsatisfiable CNF of size polynomial in n" → ¬ Satisfiable (G ∘ Sel_q) ∧ encLength (G ∘ Sel_q) ≤ n^k; reason: the sentence asserts both
--   - encoding: "no PC refutation of degree cn" → ¬ PCDerivable F ⌊c n⌋₊ 1 (base definition: formal degree, Boolean axioms y_i² + y_i); reason: formal degrees are integers, so degree ≤ cn means degree ≤ ⌊cn⌋; same instances
--   - generalization: lines as disjunctions of equations, with weakening and contraction as rules → lines as finite sets of polynomials (RLine), contraction and reordering built in; reason: each line of a refutation in the paper's form maps to its set of polynomials, and every rule application maps to a rule application, so a paper refutation gives a set-based one with the same number of lines (and the same total size); the lower bound for set-based refutations specializes to the source
--   - encoding: q = N = nℓ; total size T; log → q = n * ℓ; totalSize π = max 1 (monomial occurrences); Real.log; reason: F has no empty clause (its complement 1 would be a degree-0 PC refutation), so G ∘ Sel_q has none and every refutation has a monomial; the floor changes no instance
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem 1.5, restated p.35 (proof p.35), first stated p.5; Theorem 1.4, p.5; Corollary 4.21, p.28; Definition 1.2, p.4

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_PC
import Definitions.Def_AC02Frege_lift
import Definitions.Def_AC02Frege_Supplement_ResPC
import Definitions.Def_AC02Frege_Supplement_selector

namespace AC02Frege.Supplement

open LiftSAParity

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower
Bounds*, manuscript (sha256 88d149fa…), Theorem 1.5 (restated p.35; first stated p.5): let `F` be a
constant-width CNF on `n` variables with no PC refutation of degree `cn`, let `G = F ∘ Maj_ℓ` with
`ℓ = Θ(log n)` chosen as in Corollary 4.21, and let `q = N` (`= nℓ`). Then `G ∘ Sel_q` is an
unsatisfiable CNF of size polynomial in `n`, and every `Res(PC)` refutation of it, with no bound on
the degree of its polynomials, has total size `T ≥ exp(Ω((log n)^{5/2}))`.

**Formalization Note** Quantified exactly as the base goal (Theorem 1.4): `ℓ = Θ(log n)` is "for all
`0 < λ₁ ≤ λ₂` and every odd `ℓ` with `λ₁ log n ≤ ℓ ≤ λ₂ log n`"; the `Ω` constant `α` and the size
exponent `k` and threshold `n₀` are chosen as in the base goal: `α` after `c, λ₁, λ₂` and before
the width `w` (the stronger reading of `Ω`), `k` and `n₀` after `w`. "No PC refutation of degree `cn`"
is `¬ PCDerivable F ⌊cn⌋ 1`; `F` is assumed unsatisfiable (Definition 1.2's "requires PC degree",
and the hypothesis of Theorem 4.20, which the proof applies). Size is the base `encLength`; `T` is
`totalSize` (monomial occurrences, floored at `1`); `log` is natural. -/
theorem theorem_1_5 :
    ∀ c : ℝ, 0 < c → ∀ lam₁ lam₂ : ℝ, 0 < lam₁ → lam₁ ≤ lam₂ →
    ∃ α : ℝ, 0 < α ∧ ∀ w : ℕ, ∃ k n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ F : CNF (Fin n), (∀ J ∈ F, J.card ≤ w) → ¬ Satisfiable F →
      ¬ AC02Frege.PCDerivable F ⌊c * n⌋₊ 1 →
    ∀ ℓ : ℕ, Odd ℓ → lam₁ * Real.log n ≤ ℓ → (ℓ : ℝ) ≤ lam₂ * Real.log n →
      ¬ Satisfiable (selSubst (AC02Frege.lift F ℓ) (n * ℓ)) ∧
      AC02Frege.encLength (selSubst (AC02Frege.lift F ℓ) (n * ℓ)) ≤ n ^ k ∧
      ∀ π : List (RLine ((Fin n × Fin ℓ) × Bool × Fin (n * ℓ))),
        IsResRefutation ⊤ (selSubst (AC02Frege.lift F ℓ) (n * ℓ)) π →
          α * Real.log n ^ ((5 : ℝ) / 2) ≤ Real.log (totalSize π) := by sorry

end AC02Frege.Supplement
