-- Prove2me | Theorems.Thm_AssocRealizations_HLClass_theorem_4_9
-- name    : AssocRealizations.HLClass.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:18:26.90899+00:00
-- url     : https://prove2.me/theorems/aba52a80-99ea-4dac-b50b-e63b12e3b8c7
-- title:
--   Theorem 4.9 — Ass^I_n(σ₁) and Ass^I_n(σ₂) are normally isomorphic iff σ₂ comes from σ₁ by reflections and reversals
-- statement:
--   Let $\sigma_1, \sigma_2 \in \{+,-\}^{n-1}$. Then the Hohlweg–Lange associahedra $\mathrm{Ass}^I_n(\sigma_1)$ and $\mathrm{Ass}^I_n(\sigma_2)$ are normally isomorphic if and only if $\sigma_2$ can be obtained from $\sigma_1$ by reflections and reversals:
--   $$\mathrm{Ass}^I_n(\sigma_1) \cong \mathrm{Ass}^I_n(\sigma_2) \iff \sigma_2 \in \{\sigma_1,\ -\sigma_1,\ \sigma_1^t,\ -\sigma_1^t\}.$$
--   Here two polytopes are normally isomorphic when some linear isomorphism sends every cone of one normal fan to a cone of the other (Definition 2.1), $-\sigma$ flips every sign and $\sigma^t$ reverses the order.
--
--   Consequently the number of normally non-isomorphic Hohlweg–Lange associahedra equals the number of sign sequences of length $n-1$ up to reflection and reversal, $2^{n-3} + 2^{\lfloor (n-3)/2\rfloor}$ for $n \ge 3$; in particular the Loday associahedron ($\sigma = (-,\dots,-)$) is not normally isomorphic to the Chapoton–Fomin–Zelevinsky associahedron (alternating $\sigma$) for $n \ge 3$.
--
--   **Formalization Note** Normal fans are encoded as the fans of the vectors $v_\delta(\sigma)$ of the Setting item, one cone per set of pairwise non-crossing diagonals of $P_{n+3}(\sigma)$; that this is the normal fan of $\mathrm{Ass}^I_n(\sigma)$ is Hohlweg–Lange's Proposition 4.3, cited by the paper. The isomorphism is required to be linear.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 17, Theorem 4.9

import Mathlib
import Definitions.Def_AssocRealizations_HLClass_Setting

namespace AssocRealizations.HLClass

open ChvatalArtGallery.FanPartition

/-- Theorem 4.9 (p. 17): the Hohlweg–Lange associahedra `Ass^I_n(σ₁)` and `Ass^I_n(σ₂)` are
normally isomorphic iff `σ₂` is obtained from `σ₁` by reflections and reversals. -/
theorem theorem_4_9 (n : ℕ) (σ₁ σ₂ : Fin (n - 1) → Bool) :
    AssocRealizations.TypesMeet.NormallyIsomorphic (hlFan n σ₁) (hlFan n σ₂) ↔ SignEquiv σ₁ σ₂ := by sorry

end AssocRealizations.HLClass
