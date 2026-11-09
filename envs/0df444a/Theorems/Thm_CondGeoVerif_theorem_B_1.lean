-- Prove2me | Theorems.Thm_CondGeoVerif_theorem_B_1
-- name    : CondGeoVerif.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:52.279196+00:00
-- url     : https://prove2.me/theorems/b0fecd04-b99e-4e1e-8a81-352f4c9dbe2f
-- title:
--   Theorem B.1 — unrestricted lower bounds $m_V+\ell>\sqrt{d-k}/(100k)$, $(d-k)/(100k^2)$
-- statement:
--   Fix a Borel rule $f:\mathbb R^k\to\{-1,1\}$, $k\ge1$, and $0<\eta<1/2$, $a=1-2\eta$. Suppose $d\ge2k$ and $J_j(A;\eta)=\gamma>0$ for some contraction $A$ and $j\in\{0,1\}$. Put $g=\gamma/2$ and
--   $$\ell=\Big\lceil\frac{128\log24}{g^2}\Big\rceil .$$
--   For every $0<\varepsilon\le\gamma/8$, any verifier that is complete with probability at least $2/3$ at the single known null
--   $$Q:\quad X\sim N(0,I_d),\qquad\mathbb E_Q[Y\mid X]=af(X_1,\dots,X_k),$$
--   and sound with probability at least $2/3$ against arbitrary Gaussian-marginal stochastic labels (with respect to $\mathcal H_{f,d}$) must satisfy
--   $$m_V+\ell>\begin{cases}\sqrt{d-k}/(100k), & j=0,\\ (d-k)/(100k^2), & j=1.\end{cases}$$
--   Outputs may be arbitrary measurable Boolean predictors; interaction, computation, communication and the malicious prover's knowledge are unrestricted, and the honest prover may use any number of samples independent of the verifier's.
--
--   Differences from the source:
--   - reading: any verifier with arbitrary interaction → IVerifier: a fixed worst-case number of rounds, measurable queries and acceptance, jointly measurable output predictors; reason: the probabilities of Definition 2.1 are defined only for measurable protocols, outputs are 'measurable Boolean predictors', and bounded stopping rules are padded (p.28)
--   - generalization: soundness against every prover → soundness hypothesis only against measurable deterministic prover strategies; reason: a weaker hypothesis; the proof's simulated honest prover is a measurable randomized strategy, a mixture of deterministic ones
--   - encoding: the null Q: X ∼ N(0, I_d), E_Q[Y | X] = af(X₁, …, X_k) → any probability measure with IsLabelLaw for the base rule f(X₁, …, X_k) and constant error probability η; reason: this property determines Q uniquely
--   - encoding: ℓ = ⌈128 log 24/g²⌉, √(d − k) → natural-number ceiling, natural logarithm, real square root of d − k; reason: Lean convention
--   - encoding: labels and rule values in {−1, 1} → Bool, with true for +1; reason: Lean convention; the same instances
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem B.1, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog
import Definitions.Def_CondGeoVerif_IVerifier

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Theorem B.1 (Unrestricted conditional-moment lower bounds)** (Chen, *The Conditional
Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.24 =
PDF p.27). Fix a Borel rule `f : ℝᵏ → {−1, 1}` and `0 < η < 1/2`. Suppose `d ≥ 2k` and
`J_j(A; η) = γ > 0` for some contraction `A` and `j ∈ {0, 1}`. Put `g = γ/2` and
`ℓ = ⌈128 log 24/g²⌉`. For every `0 < ε ≤ γ/8`, any verifier that is complete with probability
at least `2/3` at the single known null `Q : X ∼ N(0, I_d)`, `E_Q[Y | X] = af(X₁, …, X_k)`, and
sound with probability at least `2/3` against arbitrary Gaussian-marginal stochastic labels, must
satisfy `m_V + ℓ > √(d − k)/(100k)` for `j = 0` and `m_V + ℓ > (d − k)/(100k²)` for `j = 1`.
Soundness is with respect to `H_{f,d}`; outputs may be arbitrary measurable predictors, and
interaction is unrestricted.

**Formalization Note** Verifiers are `IVerifier`s (any number of rounds, measurable queries and
improper measurable outputs); soundness is against every measurable prover strategy, which includes
the paper's simulated honest prover. The null `Q` is given through its characterizing property:
Gaussian marginal and `Y ≠ f(X₁, …, X_k)` with probability exactly `η`, independently of `X`.
`log` is the natural logarithm and `⌈·⌉` the natural-number ceiling. -/
theorem theorem_B_1 {k d : ℕ} (hk : 1 ≤ k) (hd : 2 * k ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η < 1 / 2) (f : Vec k → Bool) (hf : Measurable f) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : IsContraction A) (j : Fin 2) (γ : ℝ) (hγ : Jprog j f f A η = γ) (hγ0 : 0 < γ)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ γ / 8) (Q : ProbabilityMeasure (Vec d × Bool))
    (hQ : IsLabelLaw (Q : Measure (Vec d × Bool)) (frameRule f (coordFrame d k)) (fun _ => η))
    (V : IVerifier d) (hcomp : ICompleteAt V Q (projClass {f} d) ε (1 / 3))
    (hsound : ISound V (projClass {f} d) ε (1 / 3)) :
    let ℓ : ℕ := ⌈128 * Real.log 24 / (γ / 2) ^ 2⌉₊
    (j = 0 → Real.sqrt ((d : ℝ) - k) / (100 * k) < (V.m : ℝ) + ℓ) ∧
    (j = 1 → ((d : ℝ) - k) / (100 * k ^ 2) < (V.m : ℝ) + ℓ) := by sorry

end CondGeoVerif
