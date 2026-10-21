-- Prove2me | Theorems.Thm_CyberShare_Sharing_symmetry_reduction
-- name    : CyberShare.Sharing.symmetry_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:41.832209+00:00
-- url     : https://prove2.me/theorems/d077d220-5fa4-4b47-a8df-6a1d5e9ea7fa
-- title:
--   Proof of Proposition 2 — symmetry reduces mutual sharing to one deviation comparison
-- statement:
--   The two firms are symmetric. Exchanging their labels exchanges investment equilibria and ex-ante profits. When investment equilibria exist under mutual sharing and after one firm stops sharing, mutual sharing is an equilibrium exactly when firm 1 cannot improve its ex-ante profit by that deviation:
--
--   $$
--   E(\pi_{N,S})\le E(\pi_{S,S}).
--   $$
--
--   The comparison applies to every equilibrium selection in both investment subgames. It turns the two sharing-stage best-response checks into one comparison of the paper's ex-ante profits.
--
--   **Formalization Note** The displayed inequality denotes the payoffs under the corresponding subgame investment equilibria; existence of those equilibria is explicit. The same statement includes the underlying firm-swap identities.
-- source:
--   August, Noh, Shamir & Shin, Cyberattacks, Operational Disruption and Investment in Resilience Measures, SSRN 4032257 (version of 2022-02-10), proof of Proposition 2, pp. A.17–A.18 (PDF 49–50), paragraph beginning ‘The increase in firm 1’s ex-ante profit’; https://ssrn.com/abstract=4032257

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace CyberShare.Sharing

/-- The symmetry observation in the proof of Proposition 2, pp. A.17–A.18 (PDF 49–50):
interchanging the firms interchanges the investment equilibria and ex-ante profits. Thus a
single firm's deviation comparison suffices for mutual sharing when all relevant investment
subgames have equilibria. -/
theorem symmetry_reduction (P : Params) (hP : P.Standing) :
    (∀ s1 s2 K1 K2, IsInvEq P s1 s2 K1 K2 ↔ IsInvEq P s2 s1 K2 K1) ∧
    (∀ K1 K2, exAnte2 P K1 K2 = exAnte1 P K2 K1) ∧
    ((∃ K1 K2, IsInvEq P .S .S K1 K2) →
     (∃ K1 K2, IsInvEq P .N .S K1 K2) →
     (IsSharingEq P .S .S ↔
       ∀ K1 K2 K1' K2', IsInvEq P .S .S K1 K2 → IsInvEq P .N .S K1' K2' →
         exAnte1 P K1' K2' ≤ exAnte1 P K1 K2)) := by sorry

end CyberShare.Sharing
