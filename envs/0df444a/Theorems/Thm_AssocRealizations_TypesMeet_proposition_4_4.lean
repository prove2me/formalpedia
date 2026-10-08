-- Prove2me | Theorems.Thm_AssocRealizations_TypesMeet_proposition_4_4
-- name    : AssocRealizations.TypesMeet.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:07.213992+00:00
-- url     : https://prove2.me/theorems/f3458222-e770-49b9-a6c8-f38f49ad1240
-- title:
--   Proposition 4.4 — alternating Hohlweg–Lange signs give the CFZ fan
-- statement:
--   Let $\sigma=(+,-,+,-,\ldots)$ be the alternating word of length $n-1$, and let $\operatorname{snake}_n$ be the fixed snake seed. The Hohlweg–Lange fan for $\sigma$ and the Santos fan for the snake are normally isomorphic:
--
--   $$\operatorname{Fan}^{I}_n(\sigma)\cong_{\mathrm{lin}}\operatorname{Fan}^{II}_n(\operatorname{snake}_n).$$
--
--   The Santos fan with this seed is the Chapoton–Fomin–Zelevinsky fan. This result supplies the existence part of the classification. **Formalization Note** Only the second assertion of Proposition 4.4 is represented; its Loday assertion is separate.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, p. 16, Proposition 4.4, second assertion; p. 18, CFZ snake seed

import Mathlib
import Definitions.Def_AssocRealizations_TypesMeet_Setting

namespace AssocRealizations.TypesMeet

open ChvatalArtGallery.FanPartition

theorem proposition_4_4 (n : ℕ) :
    NormallyIsomorphic (hlFan (altSigma n)) (santosFan (snake n)) := by sorry
end AssocRealizations.TypesMeet
