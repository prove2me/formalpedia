-- Prove2me | Theorems.Thm_ConstrInfoDesign_Cav_rubin_wesler_step
-- name    : ConstrInfoDesign.Cav.rubin_wesler_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:19.597979+00:00
-- url     : https://prove2.me/theorems/c826af20-b689-4e38-85b4-1b5bd88f992a
-- title:
--   Proof of Proposition A.1, p. 24 — the mean (µ0, f⋆, ḡ⋆) lies in the convex hull of the graph of (f, ḡ) over supp τ (Rubin–Wesler)
-- statement:
--   Let $\tau \in \Delta_{\mu_0}(\Delta(\Omega))$ be a Borel probability measure on the belief simplex with mean $\mu_0$, and suppose $f$ and every constraint function $\bar g_k$ are $\tau$-integrable. Write $f^\star = \int f \, d\tau$ and $\bar g^\star = \int \bar g \, d\tau$, and let
--   $$B = \{(\mu, f(\mu), \bar g(\mu)) : \mu \in \operatorname{supp} \tau\} \subseteq \mathbb R^{N+1+I+E}.$$
--   Then
--   $$(\mu_0, f^\star, \bar g^\star) \in \operatorname{conv} B,$$
--   the convex hull itself, not its closure.
--
--   This is the step of the proof of Proposition A.1 that invokes Rubin and Wesler (1958): the mean of an integrable random vector in a finite-dimensional space lies in the convex hull of any set carrying it almost surely. It is what lets a general distribution over posteriors be replaced by one with finite support.
--
--   **Formalization Note** The support is Mathlib's `Measure.support` (the points all of whose neighbourhoods have positive measure). The constraint inequalities of CID, mentioned in the page's sentence "By assumption, …", are not needed for this step and are not hypotheses. Integrability of $f$ and of the $\bar g_k$ is stated explicitly; the paper leaves it implicit.
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, p. 24, proof of Proposition A.1

import Mathlib
import Definitions.Def_ConstrInfoDesign_Cav_Model

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- Proof of Proposition A.1 (Doval–Skreta, arXiv:1811.03588v3, p. 24): for a Bayes-plausible `τ`
with `f` and every `ḡ_k` integrable, the mean `(µ0, f⋆, ḡ⋆)` of `µ ↦ (µ, f(µ), ḡ(µ))` lies in the
convex hull (not its closure) of `B = {(µ, f(µ), ḡ(µ)) : µ ∈ supp τ}` (Rubin–Wesler 1958). -/
theorem rubin_wesler_step {N nI nE : ℕ} (f : (Fin N → ℝ) → ℝ) (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) (mu0 : Fin N → ℝ) (τ : Measure (Fin N → ℝ)) (hτ : IsBayesPlausible mu0 τ) (hf : Integrable f τ) (hgI : ∀ i, Integrable (gI i) τ) (hgE : ∀ e, Integrable (gE e) τ) : (mu0, (∫ mu, f mu ∂τ, ((fun i => ∫ mu, gI i mu ∂τ), (fun e => ∫ mu, gE e mu ∂τ)))) ∈ convexHull ℝ ((fun mu => (mu, (f mu, ((fun i => gI i mu), (fun e => gE e mu))))) '' τ.support) := by sorry

end ConstrInfoDesign.Cav
