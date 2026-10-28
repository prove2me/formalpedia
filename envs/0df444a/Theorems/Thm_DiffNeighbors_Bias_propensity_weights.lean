-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_propensity_weights
-- name    : DiffNeighbors.Bias.propensity_weights
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:18.673602+00:00
-- url     : https://prove2.me/theorems/9580f1fd-2640-488f-8f67-cb2a480a5c7c
-- title:
--   §3.3, p. 11 — propensity weights: F¹(p) = E[(Z_i/p)Y_i], F⁰(p) = E[((1−Z_i)/(1−p))Y_i], E[f^a(Z)|Z_j = b] = E[1{Z_i=a}1{Z_j=b}Y_i/(Pr(Z_i=a)Pr(Z_j=b))]
-- statement:
--   Under the Bernoulli design ($Z_l$ i.i.d. Bernoulli$(p)$, $0 < p < 1$), let $Y_i = f_i(Z)$ and let $f^a_i$ be unit $i$'s conditional outcome function. Then
--
--   1. $F^1(p) = \mathbb E[f^1_i(Z)] = \mathbb E\bigl[\tfrac{Z_i}{p} Y_i\bigr]$;
--   2. $F^0(p) = \mathbb E[f^0_i(Z)] = \mathbb E\bigl[\tfrac{1 - Z_i}{1 - p} Y_i\bigr]$;
--   3. for every unit $j \neq i$ and all $a, b \in \{0,1\}$,
--   $$\mathbb E[f^a_i(Z) \mid Z_j = b] = \mathbb E\Bigl[\frac{\mathbf 1\{Z_i = a\}}{\Pr(Z_i = a)} \frac{\mathbf 1\{Z_j = b\}}{\Pr(Z_j = b)} Y_i\Bigr],$$
--   with $\Pr(Z_i = 1) = p$ and $\Pr(Z_i = 0) = 1 - p$.
--
--   These identities show that every term of the first-order approximation to the ATE can be estimated from the observed outcomes by inverse-propensity weighting; this is how the DN estimator is derived.
--
--   Differences from the source:
--   - generalization: j ∈ N_i (so j ≠ i) and outcomes under Assumption 1 (standing) → every j ≠ i and any outcome functions, with no Assumption 1; reason: the identity uses only the independence of the design; it specializes to j ∈ N_i, where i ∉ N_i gives j ≠ i
--   - encoding: a Bernoulli(p) design whose weights divide by p and 1 − p → hypotheses 0 < p and p < 1; reason: the weights 1/p and 1/(1 − p) and the design presuppose p ∈ (0,1); this only excludes undefined cases
--   - encoding: E[·] over z_i i.i.d. Bernoulli(p) → bernExp p h = Σ_z (Π_j (p if z_j = 1 else 1 − p)) h(z), a finite sum; reason: the law of the design on the finite set {0,1}^N; same values
--   - encoding: f^a_i as a function of z_{N_i}; E[f^a(Z) | Z_j = b] and E[f^a(Z) | Z_j = b, Z_k = c] → condOutcome f i a z = f_i(z with z_i := a), a function on all of {0,1}^N; conditional expectations are bernExp of the function with the conditioned coordinates overwritten by Function.update; reason: under Assumption 1 condOutcome f i a depends only on z_{N_i}; by independence of the coordinates, conditioning on Z_j = b is the same as setting z_j := b
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 11, §3.3 (proof of Theorem 1), displays 'F¹(p) = E[f¹(Z)] = E[(Z_i/p)Y_i]', 'F⁰(p) = …' and 'E[f^a(Z)|Z_j = b] = E[…]'

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **Propensity weights**, §3.3, p. 11: under the Bernoulli(`p`) design,
(i) `F¹_i(p) = E[f¹_i(Z)] = E[(Z_i/p) Y_i]`, (ii) `F⁰_i(p) = E[f⁰_i(Z)] = E[((1 − Z_i)/(1 − p)) Y_i]`, and
(iii) for `a, b ∈ {0, 1}` and `j ≠ i`,
`E[f^a_i(Z) | Z_j = b] = E[(1{Z_i = a}/Pr(Z_i = a)) (1{Z_j = b}/Pr(Z_j = b)) Y_i]`. -/
theorem propensity_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → (ι → Bool) → ℝ) (i : ι) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    bernExp p (condOutcome f i true) = bernExp p (fun z => ind (z i) / p * f i z) ∧
    bernExp p (condOutcome f i false) = bernExp p (fun z => (1 - ind (z i)) / (1 - p) * f i z) ∧
    ∀ (j : ι), j ≠ i → ∀ a b : Bool,
      bernExp p (fun z => condOutcome f i a (Function.update z j b)) =
        bernExp p (fun z => (if z i = a then (1 : ℝ) else 0) / bernProb p a *
          ((if z j = b then (1 : ℝ) else 0) / bernProb p b) * f i z) := by sorry

end DiffNeighbors.Bias
