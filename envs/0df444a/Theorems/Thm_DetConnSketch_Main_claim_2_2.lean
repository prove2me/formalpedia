-- Prove2me | Theorems.Thm_DetConnSketch_Main_claim_2_2
-- name    : DetConnSketch.Main.claim_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:06.98946+00:00
-- url     : https://prove2.me/theorems/a756876a-f5a2-45fc-88dc-b69ee45bde31
-- title:
--   Claim 2.2 — the one-way connected-components complexity lies between $\log_2\chi(P_n)$ and $\lceil\log_2\chi(P_n)\rceil$
-- statement:
--   Let $P_n$ be the universal graph on $n$ labeled vertices. The deterministic one-way connected-components complexity $\mathrm{CC}_n$ satisfies $\log_2 \chi(P_n) \le \mathrm{CC}_n \le \lceil \log_2 \chi(P_n)\rceil$, in the two explicit forms
--   $$\text{(lower)}\ \ \text{an } m\text{-bit protocol exists} \Rightarrow P_n \text{ is } 2^m\text{-colourable}; \qquad \text{(upper)}\ \ P_n \text{ is } c\text{-colourable} \Rightarrow \text{a } \lceil\log_2 c\rceil\text{-bit protocol exists}.$$
--   Hence the complexity is $\Theta(\log \chi(P_n))$.
--
--   The lower half turns the chromatic lower bound of Theorem 8.1 into a lower bound on messages.
--
--   Differences from the source:
--   - generalization: the complexity is Θ(log(χ(P_n))) → both bounds of the proof explicitly: an m-bit protocol ⇒ P_n is (2^m)-colourable, and P_n c-colourable ⇒ a protocol with Nat.clog 2 c = ⌈log₂ c⌉ bits; reason: the explicit bounds log₂ χ ≤ complexity ≤ ⌈log₂ χ⌉ imply Θ; this is what the proof shows
--   - encoding: χ(P_n) and 'complexity' → SimpleGraph.Colorable of universalGraph (Fin n), and Nonempty (CompProtocol (Fin n) m); reason: χ is the least c with Colorable c
--   - encoding: same connected components → equal reachability relations of GA \ GB on all of Fin n; reason: the components are the classes of reachability
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 14 (PDF 18), Claim 2.2 and proof

import Mathlib
import Definitions.Def_DetConnSketch_Main_Protocol
import Definitions.Def_DetConnSketch_Main_UniversalGraph

namespace DetConnSketch.Main

/-- Claim 2.2, in the explicit two-sided form of its proof: (lower) if a deterministic one-way
connected-components protocol on `Fin n` with `m`-bit messages exists, then `P_n` is
`2^m`-colourable, i.e. `χ(P_n) ≤ 2^m`; (upper) if `P_n` is `c`-colourable, there is such a
protocol with `⌈log₂ c⌉`-bit messages. Together: the least message length lies between
`log₂ χ(P_n)` and `⌈log₂ χ(P_n)⌉`. -/
theorem claim_2_2 (n : ℕ) :
    (∀ m : ℕ, Nonempty (CompProtocol (Fin n) m) → (universalGraph (Fin n)).Colorable (2 ^ m)) ∧
    (∀ c : ℕ, (universalGraph (Fin n)).Colorable c →
      Nonempty (CompProtocol (Fin n) (Nat.clog 2 c))) := by sorry

end DetConnSketch.Main
