-- Prove2me | Theorems.Thm_AvoidPlast_padding_derandomization
-- name    : AvoidPlast.padding_derandomization
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:50:04.273912+00:00
-- url     : https://prove2.me/theorems/683b4403-0711-4394-800b-e26050650d9d
-- title:
--   Proof of Theorem 5.8: prBP$^*$L = prL gives prBP$^*$SPACE$[O(s)]$ = prDSPACE$[O(s)]$ by padding
-- statement:
--   If $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$, then for every space bound $s(n)\ge\log_2(n+2)$ computable in space $O(s(n))$, a promise problem is in $\mathrm{prBP}^*\mathrm{SPACE}[O(s)]$ if and only if it is in $\mathrm{prDSPACE}[O(s)]$. This is the derandomization step of the main theorem, used for $s(n)=\lceil n^\gamma\rceil$.
--
--   Differences from the source:
--   - reading: $\mathrm{prBP}^*\mathrm{SPACE}[O(n^\gamma)]=\mathrm{prDSPACE}[O(n^\gamma)]$ "by a standard padding argument", for the $\gamma$ of the proof → every $s\ge\log_2(n+2)$ computable in space $O(s)$, which covers $\lceil n^\gamma\rceil$ for rational $\gamma$; reason: the paper's nice-function convention (p.14); padding must compute the padded length, the proofs may pick a smaller rational exponent, and $\lceil n^\gamma\rceil$ and $n^\gamma$ give the same $O(\cdot)$; reading R7
--   - encoding: persistent two-way read-only random tape of unstated length → a random string of the fixed length of the machine's time bound, $C(n^C+1)$, with a head that may also jump; reason: a free length function would be non-uniform advice and would make $\mathrm{prBP}^*\mathrm{L}=\mathrm{prL}$ false; a jump is simulated by a walk within polynomial time and logspace
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Proof of Theorem 5.8, p.25

import Mathlib
import Definitions.Def_KarpLiptonOM_PromiseProblem
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_InPrBPstarSpace
import Definitions.Def_AvoidPlast_InPrDSpace
import Definitions.Def_AvoidPlast_PrBPstarLEqPrL
import Definitions.Def_AvoidPlast_IsSpaceConstructible

namespace AvoidPlast

/-- Space-bounded derandomization by padding (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), proof of Theorem 5.8, p.25, "by a standard padding
argument"): if `prBP*L = prL` then `prBP*SPACE[O(s)] = prDSPACE[O(s)]`, for every bound
`s(n) ≥ log₂(n + 2)` computable in space `O(s(n))`. Reading R7. -/
theorem padding_derandomization (hyp : PrBPstarLEqPrL) (s : ℕ → ℕ)
    (hs : ∀ n, lg n ≤ s n) (hc : IsSpaceConstructible s) (P : KarpLiptonOM.PromiseProblem) :
    InPrBPstarSpace (fun n => (s n : ℝ)) P ↔ InPrDSpace (fun n => (s n : ℝ)) P := by sorry

end AvoidPlast
