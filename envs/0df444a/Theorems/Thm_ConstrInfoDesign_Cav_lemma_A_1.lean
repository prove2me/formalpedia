-- Prove2me | Theorems.Thm_ConstrInfoDesign_Cav_lemma_A_1
-- name    : ConstrInfoDesign.Cav.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:22.487045+00:00
-- url     : https://prove2.me/theorems/ba185f28-a8e0-4e78-9e95-d3cfe7f056b3
-- title:
--   Lemma A.1, p. 24 — the feasibility set F is the convex hull of the pointwise-constraint set C
-- statement:
--   The set $\mathcal F$ of parameters $(\mu, \tilde\gamma)$ at which CID is feasible (Definition 2.2) is the convex hull of the effective domain $C$ of $f^{\bar g}$, the set where the constraints hold pointwise:
--   $$\mathcal F = \operatorname{conv} C, \qquad C = \{(\mu, \tilde\gamma) \in \Delta(\Omega) \times \mathbb R^{I+E} : \bar g_I(\mu) \ge \tilde\gamma_I,\ \bar g_E(\mu) = \tilde\gamma_E\}.$$
--
--   The lemma identifies the effective domain of $\operatorname{cav} f^{\bar g}$ with the feasibility set, and a step of its proof reappears in the proof of Theorem 3.1.
--
--   **Formalization Note** Feasibility in $\mathcal F$ requires every $\bar g_k$ to be integrable under the witnessing distribution (the paper leaves this implicit). No measurability hypothesis on $\bar g$ is stated: the identity holds for arbitrary $\bar g$ with this convention.
-- source:
--   Doval and Skreta, Constrained Information Design, arXiv:1811.03588v3, p. 24, Lemma A.1

import Mathlib
import Definitions.Def_ConstrInfoDesign_Cav_Model

namespace ConstrInfoDesign.Cav

open MeasureTheory

/-- Lemma A.1 (Doval–Skreta, arXiv:1811.03588v3, p. 24): the feasibility set `F` (Definition 2.2)
is the convex hull of the set `C` where the constraints hold pointwise, `F = conv C`. -/
theorem lemma_A_1 {N nI nE : ℕ} (gI : Fin nI → (Fin N → ℝ) → ℝ) (gE : Fin nE → (Fin N → ℝ) → ℝ) : feasibleSet gI gE = convexHull ℝ (pointwiseSet gI gE) := by sorry

end ConstrInfoDesign.Cav
