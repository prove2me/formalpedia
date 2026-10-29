-- Prove2me | Theorems.Thm_BitcoinMalleability_p2sh_wrapped_scriptSig
-- name    : BitcoinMalleability.p2sh_wrapped_scriptSig
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T00:02:45.315236+00:00
-- url     : https://prove2.me/theorems/ab9d92a6-9587-45bf-b1f5-c03a7ff8f778
-- title:
--   A P2SH-wrapped witness spend has the single push of its witness program as scriptSig
-- statement:
--   For `VerifyScript` with the `P2SH` and `WITNESS` flags, a P2SH `scriptPubKey`, a non-empty witness and a `scriptSig` on which it succeeds: the `scriptSig` evaluates to a stack whose top element `redeem` is a witness program, and the `scriptSig` is exactly the single push of `redeem` (`SCRIPT_ERR_WITNESS_MALLEATED_P2SH` otherwise). The `scriptSig` of a wrapped witness spend is therefore determined by the redeem script the output's hash commits to.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript (SCRIPT_ERR_WITNESS_MALLEATED, SCRIPT_ERR_WITNESS_MALLEATED_P2SH), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CTransaction::ComputeHash, SerializeTransaction (primitives/transaction.h, transaction.cpp); CheckInputScripts (validation.cpp); BIP141 (Transaction ID)

import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinVerify
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.p2sh_wrapped_scriptSig (tap : BitcoinVerify.TaprootHandler) (c : BitcoinVerify.Ctx)
    (sig spk : BitcoinSer.Bytes) (w : List BitcoinSer.Bytes) (hp : c.flags.p2sh = true) (hf : c.flags.witness = true)
    (hspk : BitcoinVerify.isPayToScriptHash spk = true) (hw : w ≠ [])
    (hv : BitcoinVerify.verifyScript tap c sig spk w = true) :
    ∃ redeem rest, BitcoinVerify.evalBytes c .base [] sig = some (redeem :: rest) ∧
      BitcoinVerify.isWitnessProgram redeem ≠ none ∧ sig = BitcoinSig.pushBytes redeem := by sorry
