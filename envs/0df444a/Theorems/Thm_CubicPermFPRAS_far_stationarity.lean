-- Prove2me | Theorems.Thm_CubicPermFPRAS_far_stationarity
-- name    : CubicPermFPRAS.far_stationarity
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:55.249199+00:00
-- url     : https://prove2.me/theorems/43eca0f2-bcda-4b97-bc10-12ba201f6da8
-- title:
--   §5.5, p.16 — the FAR chain is lazy, irreducible and reversible; $\pi_B(\cdot\mid\mathcal P)=\mu$ and $\pi_B(\mathcal P)\ge1/(1+8\alpha^2)$
-- statement:
--   Let $\lambda$ be positive activities, $r$ an anchor, $\alpha>1$, $w(r,\cdot)$ $\alpha$-rough anchor weights and $B$ the rescaled matrix. The FAR transition matrix $P_{\mathrm{FAR}}$ has nonnegative entries and
--
--   1. is lazy ($P_{\mathrm{FAR}}(M,M)\ge1/2$), irreducible, and reversible with respect to $\pi_B$, which is a stationary distribution;
--   2. $\pi_B(\cdot\mid\mathcal P)=\mu$, the $\lambda$-weighted distribution on perfect matchings;
--   3. $\pi_B(\mathcal P)\ge1/(1+8\alpha^2)$;
--   4. $\sum_{u,v}W(u,v)\le4n^2$ and $B(\mathcal N(u,v))\le2\alpha^2B(\mathcal P)$.
--
--   The first two facts let FAR frequencies recalibrate the anchor weights; the third makes the sampler's output a warm start.
--
--   Differences from the source:
--   - encoding: irreducible → $\forall\,\sigma,\tau\ \exists t,\ P_{\mathrm{FAR}}^t(\sigma,\tau)>0$; reason: the standard meaning
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), §5.5, p.16 (PDF 18), unnumbered display

import Mathlib
import Definitions.Def_CubicPermFPRAS_farChain

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **The FAR chain's stationary distribution**, §5.5, p.16 (PDF 18), unnumbered display,
X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

The chain is lazy, irreducible, and reversible with stationary distribution `π_B`. Moreover,
`π_B(· | P) = µ` and `π_B(P) ≥ 1/(1 + 8α²)`; indeed `∑_{u,v} W(u,v) ≤ 4n²` and
`B(N(u,v)) ≤ 2α² B(P)`.

**Formalization Note.** `P_FAR` is the matrix `farP` of the transition probabilities printed on
p.16 (self-loop = remaining mass); its entries are nonnegative. Irreducibility is
`∀ σ τ, ∃ t, P^t(σ,τ) > 0`. Hypotheses: positive activities, `α`-rough anchor weights (§5.5,
p.15). -/
theorem far_stationarity (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 1 < α)
    (lam : Matrix (Fin n) (Fin n) ℝ) (hlam : ∀ u v, 0 < lam u v) (r : Fin n) (w : Fin n → ℝ)
    (hw : IsRoughAnchor α lam r w) :
    (∀ σ τ : Omega n, 0 ≤ farP (Bmat lam w) σ τ) ∧
    (∀ σ : Omega n, 1 / 2 ≤ farP (Bmat lam w) σ σ) ∧
    (∀ σ τ : Omega n, ∃ t : ℕ, 0 < (farP (Bmat lam w) ^ t) σ τ) ∧
    (∀ σ τ : Omega n, piB (Bmat lam w) σ * farP (Bmat lam w) σ τ =
      piB (Bmat lam w) τ * farP (Bmat lam w) τ σ) ∧
    ((∀ σ, 0 ≤ piB (Bmat lam w) σ) ∧ ∑ σ, piB (Bmat lam w) σ = 1 ∧
      Matrix.vecMul (piB (Bmat lam w)) (farP (Bmat lam w)) = piB (Bmat lam w)) ∧
    (∀ σ : Omega n, IsPerfect σ.1 →
      piB (Bmat lam w) σ / (∑ τ : Omega n, if IsPerfect τ.1 then piB (Bmat lam w) τ else 0) =
        muPM lam σ.1) ∧
    1 / (1 + 8 * α ^ 2) ≤ (∑ τ : Omega n, if IsPerfect τ.1 then piB (Bmat lam w) τ else 0) ∧
    ∑ u, ∑ v, Wfar (Bmat lam w) u v ≤ 4 * (n : ℝ) ^ 2 ∧
    ∀ u v : Fin n,
      familyWeight (Bmat lam w) (NSet u v) ≤ 2 * α ^ 2 * familyWeight (Bmat lam w) (PSet n) := by sorry

end CubicPermFPRAS
