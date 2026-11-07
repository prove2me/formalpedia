-- Prove2me | Theorems.Thm_FairKMeans_lemma_18
-- name    : FairKMeans.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:32:42.284771+00:00
-- url     : https://prove2.me/theorems/ccd5107f-e71f-4e50-a7c1-4e54ad81dcc4
-- title:
--   Lemma 18 — column identity: the linearized cost splits into one LP-friendly term per column
-- statement:
--   Let $(T,\phi_T)$ be a relaxed solution with $u_p$, $p_\lambda$ defined by (26), and let $(T',\phi_{T'})$ be a relaxed solution. For every candidate $t\in T'$, with $\pi(t)$ its centroid in $\phi_{T'}$,
--
--   $$\sum_{p}\phi_{T'}(p,t)\Big(\|p-\pi(t)\|^2+2\lambda(\nu_p-p)^\top(\pi(t)-p)\Big)=\min_{c\in\mathbb R^d}\sum_p\phi_{T'}(p,t)\|p_\lambda-c\|^2-\min_{v\in\mathbb R^d}\sum_p\phi_{T'}(p,t)\|u_p-v\|^2, \tag{27}$$
--
--   and consequently
--
--   $$L(\phi_{T'})=\sum_{t\in T'}\Big(\min_{c}\sum_p\phi_{T'}(p,t)\|p_\lambda-c\|^2-\min_{v}\sum_p\phi_{T'}(p,t)\|u_p-v\|^2\Big). \tag{28}$$
--
--   This turns each iteration of Algorithm 1 into the linear program (29).
--
--   Differences from the source:
--   - encoding: min over c, v ∈ ℝ^d → real infima ⨅ over E d; reason: the minima are attained at weighted centroids
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 18, (27)–(28), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution

namespace FairKMeans

/-- **Lemma 18 (Column identity)**, p.24 (PDF 26). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held
version, sha256 73e9312c…).

With `u_p`, `p_λ` defined by (26) for the relaxed solution `φ`, and `φ'` another relaxed
solution, every candidate `t` of `φ'` satisfies (27)
`∑_p φ'(p,t)(‖p − π(t)‖² + 2λ(ν_p − p)ᵀ(π(t) − p)) = min_c ∑_p φ'(p,t)‖p_λ − c‖² − min_v ∑_p φ'(p,t)‖u_p − v‖²`,
with `π(t)` the centroid of `t` in `φ'`; consequently (28) `L(φ')` is the sum over `t` of the
right-hand sides.

**Formalization Note.** The minima over `ℝ^d` are written `⨅`; they are attained at weighted
centroids. -/
theorem lemma_18 {d n m s s' : ℕ} (I : Instance d n m) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (φ : Fin n → Fin s → ℝ) (φ' : Fin n → Fin s' → ℝ) (h : IsRelaxed I φ) (h' : IsRelaxed I φ') :
    (∀ t : Fin s',
      ∑ p, φ' p t * (‖I.pts p - cen I φ' t‖ ^ 2
          + 2 * lam ρ * inner ℝ (nu I φ p - I.pts p) (cen I φ' t - I.pts p)) =
        (⨅ c : E d, ∑ p, φ' p t * ‖plam I ρ φ p - c‖ ^ 2)
          - ⨅ v : E d, ∑ p, φ' p t * ‖uvec I ρ φ p - v‖ ^ 2) ∧
      linCost I ρ φ φ' =
        ∑ t : Fin s', ((⨅ c : E d, ∑ p, φ' p t * ‖plam I ρ φ p - c‖ ^ 2)
          - ⨅ v : E d, ∑ p, φ' p t * ‖uvec I ρ φ p - v‖ ^ 2) := by sorry

end FairKMeans
