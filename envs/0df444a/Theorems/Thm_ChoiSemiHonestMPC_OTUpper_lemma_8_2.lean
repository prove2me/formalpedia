-- Prove2me | Theorems.Thm_ChoiSemiHonestMPC_OTUpper_lemma_8_2
-- name    : ChoiSemiHonestMPC.OTUpper.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:29:50.722854+00:00
-- url     : https://prove2.me/theorems/d637b6f4-094a-43c1-a571-ee3908950e32
-- title:
--   Lemma 8.2 — private conversion with adaptive corruption
-- statement:
--   Let `pre` be an input-independent preprocessing protocol producing $\ell$ ROT pairs, and suppose two things. (i) Under every adversary, its outputs are almost surely consistent ROT outputs ($(U_0,U_1)$ and $(C,U_C)$), and every server ends preprocessing in one fixed blank state (servers have erased; they take no further part). (ii) For either fixed client $P$ and every strategy controlling adaptive server corruptions and scheduling, $P$'s complete preprocessing view and the strategy's state can be reconstructed from $P$'s prescribed ideal ROT outputs, jointly with both ROT outputs, with error at most $\varepsilon$. Then preprocessing followed by the three-bit conversion is $4\varepsilon$-secure in the sense of Definition 2.1 against passive adaptive rushing adversaries corrupting at most one client and $t$ servers. The synchronous-round requirement is explicit. The conclusion also asserts the same bound for the concrete straight-line simulator of the proof: it samples preprocessing honestly, attaches the actual corrupted input at the first client corruption, and instantiates the private conversion without conditioning or rewinding.
--
--   Differences from the source:
--   - reading: (i) preprocessing produces consistent ROT outputs and no application outputs; all servers erase and stop before conversion → almost surely consistent ROT outputs under every adversary; every server’s final preprocessing state equals one fixed blank state; servers are idle in the conversion by construction (embed); reason: erasure means no information remains; a fixed state carries none
--   - reading: (ii) reconstruction from P’s prescribed ideal ROT outputs with error ε → FixedClientSim pre t P 0 0 ε (wROT with revelation probability 0 is ROT); reason: the same notion
--   - encoding: with a straight-line simulator using no conditional-distribution sampler → IsSecure and ConversionSimulates for the explicit conversionSimulator; reason: the source proof samples preprocessing honestly, then instantiates private conversion data using the corrupted client’s input and prescribed output; the simulator uses original sampling operations, no conditional law or rewinding, and the online harness preserves disclosed prefixes
--   - encoding: synchronous network model inherited from Section 2.1 → pre.Synchronous: all messages and local operations of each round finish by its deadline; reason: an arbitrary Protocol structure has an unchecked opBound field; this condition states the source’s round-completion requirement rather than an additional cryptographic hypothesis
--   - reading: the network model of Section 2 (synchronous private channels; separate send, receive and erase operations; corruption between operations; rushing; permitted scheduling) → `Protocol` / `realExec`: operation-level scheduling and corruption, including receipt from a selected sender; private traffic is hidden; state replacement models erasure, with a separate delivery-gated operation for Figure 5; round deadlines complete the remaining operations; reason: the synchronous private-channel model permits these interleavings; Synchronous records completion of each round for abstract preprocessing and postprocessing protocols
--   - encoding: distributions of protocol executions → discrete distributions (`PMF`); statistical distance is ½‖·‖₁ (`tvPMF`); probabilities and expectations via `probE` / `expectE` (expectation in ℝ≥0∞); reason: every protocol variable is discrete, and on discrete spaces ½‖·‖₁ is the statistical distance
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Lemma 8.2, p. 41-42 (PDF 43-44)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Security

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-- Lemma 8.2 (private conversion with adaptive corruption). -/
theorem lemma_8_2 {n ℓ : ℕ}
    (pre : Protocol n Unit Unit (Bits ℓ × Bits ℓ) (Bits ℓ × Bits ℓ)) (t : ℕ) (ε : ℝ)
    (h_sync : pre.Synchronous)
    (h_cons : ∀ (Aux : Type) (A : Adversary n pre.S Aux) (aux : Aux) (fixed : Option Client),
      probE (pre.realExec t A aux () () fixed) (fun cfg =>
        ¬ ∃ u0 u1 c : Bits ℓ, pre.outA (cfg.st .alice) = some (u0, u1) ∧
          pre.outB (cfg.st .bob) = some (c, selBits c u0 u1)) = 0)
    (h_erase : ∃ blank : pre.S, ∀ (Aux : Type) (A : Adversary n pre.S Aux) (aux : Aux)
      (fixed : Option Client),
      probE (pre.realExec t A aux () () fixed) (fun cfg => ∃ i, cfg.st (.server i) ≠ blank) = 0)
    (h_rec : ∀ P : Client, FixedClientSim pre t P 0 0 ε) :
    IsSecure (Protocol.seq pre (Protocol.embed (convProto ℓ)) (fun _ => ()) (fun _ => ()))
      t (otFun ℓ) (4 * ε) ∧ ConversionSimulates pre t (4 * ε) := by sorry

end ChoiSemiHonestMPC.OTUpper
