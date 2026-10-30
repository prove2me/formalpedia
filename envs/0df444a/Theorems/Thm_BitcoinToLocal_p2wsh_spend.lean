-- Prove2me | Theorems.Thm_BitcoinToLocal_p2wsh_spend
-- name    : BitcoinToLocal.p2wsh_spend
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:10:18.958995+00:00
-- url     : https://prove2.me/theorems/7e76b6bb-6c64-489e-82c7-d833a79e9b7e
-- title:
--   The to_local output under VerifyScript: a witness spends it iff it is a signature, a selector and the script, and the selected branch holds
-- statement:
--   For a context with the `WITNESS` flag, keys of at most 520 bytes, $|{\rm delay}| < 2^{32}$ and any witness `ws`: `verifyScript tap c [] (witnessBytes 0 (sha256 (toLocalBytes rev delay dpk))) (ws ++ [toLocalBytes rev delay dpk]) = true` if and only if `castToBool (sha256 (toLocalBytes rev delay dpk)) = true` and there are $b$, `sig` with `ws = [sig, b]`, both of at most 520 bytes, and `SpendCondition` for the flags of $c$ and the signature mission's `legacyOracle` of $c$'s transaction, input, amount and `SigVersion::WITNESS_V0` on the script. So the output is spent only by the revocation key, or by the delayed key after the sequence check; the first conjunct is `VerifyScript`'s requirement that the program be a true value.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.p2wsh_spend (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (hf : c.flags.witness = true) (rev dpk : Bytes) (delay : Int) (ws : List Bytes)
    (hrev : rev.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (hdpk : dpk.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE)
    (hd : delay.natAbs < 2 ^ 32) :
    BitcoinVerify.verifyScript tap c [] (BitcoinVerify.witnessBytes 0 (BitcoinSer.sha256 (BitcoinToLocal.toLocalBytes rev delay dpk)))
        (ws ++ [BitcoinToLocal.toLocalBytes rev delay dpk]) = true ↔
      BitcoinScript.castToBool (BitcoinSer.sha256 (BitcoinToLocal.toLocalBytes rev delay dpk)) = true ∧
      ∃ b sig, ws = [sig, b] ∧ sig.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE ∧ b.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE ∧
        BitcoinToLocal.SpendCondition (BitcoinVerify.scriptFlagsOf c.flags)
          (BitcoinSig.legacyOracle (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 (BitcoinToLocal.toLocalBytes rev delay dpk))
          rev delay dpk b sig := by sorry
