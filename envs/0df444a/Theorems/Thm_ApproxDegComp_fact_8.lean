-- Prove2me | Theorems.Thm_ApproxDegComp_fact_8
-- name    : ApproxDegComp.fact_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:55.779964+00:00
-- url     : https://prove2.me/theorems/6319bab8-9cdb-4b6e-b51e-b419d8c8b1ce
-- title:
--   Fact 8 — dual witness characterization of $\widetilde{\deg}(g)\ge d$
-- statement:
--   Let $g:\{0,1\}^m\to\{0,1\}$ be a non-constant Boolean function and $d\in\mathbb N$. Then $\widetilde{\deg}(g)\ge d$ if and only if there is a real function $\psi$ on $\{0,1\}^m$ such that
--
--   1. $\|\psi\|_1=\sum_x|\psi(x)|=1$;
--   2. $\langle\psi,p\rangle=\sum_x\psi(x)p(x)=0$ for every real polynomial $p$ of degree $<d$;
--   3. $\langle\psi,g\rangle=\sum_x\psi(x)g(x)>1/3$.
--
--   This is linear-programming duality for the approximation problem; Lemma 20 builds its projectors from such a witness.
--
--   **Formalization Note** Inner products are unnormalized sums over the cube, with $p$ evaluated at the 0/1 points; degree is total degree; both directions are stated for every $d$.
--
--   Differences from the source:
--   - encoding: {0,1}^m → ι → Bool for an arbitrary finite type ι; reason: every finite index set is in bijection with [m]; same instances
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Fact 8, p.16

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg

namespace ApproxDegComp

/-- **Fact 8 (Dual witness [12, 13, 40])**, p.16.
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Fact 8, p.16: "Let g : {0, 1}^m → {0, 1} be a non-constant Boolean function. d̃eg(g) ≥ d if
and only if there exists a real function ψ on {0, 1}^m such that ‖ψ‖₁ = 1; (2) ⟨ψ, p⟩ = 0 for
every polynomial p of degree < d; (3) ⟨ψ, g⟩ > 1/3. (4)"

**Formalization Note** `⟨ψ, p⟩ = Σ_x ψ(x) p(x)` over the cube (the paper's unnormalized inner
product, p.10), with `p` a real polynomial evaluated at the 0/1 points; `⟨ψ, g⟩` uses
`g`'s 0/1 values. Both directions, for every `d ∈ ℕ`. -/
theorem fact_8 {ι : Type} [Fintype ι] [DecidableEq ι] (g : (ι → Bool) → Bool) (hg : ∃ x y, g x ≠ g y) (d : ℕ) :
    d ≤ approxDeg g ↔ ∃ ψ : (ι → Bool) → ℝ, ∑ x, |ψ x| = 1 ∧
      (∀ p : MvPolynomial ι ℝ, p.totalDegree < d →
        ∑ x, ψ x * MvPolynomial.eval (cubePt x) p = 0) ∧
      1 / 3 < ∑ x, ψ x * boolToReal (g x) := by sorry

end ApproxDegComp
