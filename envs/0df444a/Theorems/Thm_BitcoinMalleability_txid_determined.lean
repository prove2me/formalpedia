-- Prove2me | Theorems.Thm_BitcoinMalleability_txid_determined
-- name    : BitcoinMalleability.txid_determined
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T00:02:32.679993+00:00
-- url     : https://prove2.me/theorems/385f6243-f4ea-4e64-96bb-d7633cc49c53
-- title:
--   Non-malleability: same intent, verifying scripts, native witness programs — same txid
-- statement:
--   For flags with `WITNESS`, a ledger $u$ and two transactions with the same intent (same version, prevouts, sequence numbers, outputs and lock time), both of whose scripts verify against $u$, where the inputs spend native witness programs: `txid tx = txid tx'`. No choice of signatures or witnesses — by the signer, or by a third party re-encoding them — changes the identifier of a valid spend. This is the BIP141 property that second-layer protocols (payment channels) rely on to refer to unconfirmed transactions by txid.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript (SCRIPT_ERR_WITNESS_MALLEATED, SCRIPT_ERR_WITNESS_MALLEATED_P2SH), src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; CTransaction::ComputeHash, SerializeTransaction (primitives/transaction.h, transaction.cpp); CheckInputScripts (validation.cpp); BIP141 (Transaction ID)

import Definitions.Def_BitcoinMalleability
import Definitions.Def_BitcoinActivation
import Definitions.Def_BitcoinSer
open BitcoinMalleability BitcoinSer BitcoinBlockV2

theorem BitcoinMalleability.txid_determined (f : BitcoinActivation.ScriptFlags) (u : Ledger)
    (tx tx' : BitcoinSer.Tx) (hf : f.witness = true)
    (hI : BitcoinMalleability.intentOf tx = BitcoinMalleability.intentOf tx')
    (h : BitcoinBlockV2.inputScriptsOk f u tx = true) (h' : BitcoinBlockV2.inputScriptsOk f u tx' = true)
    (hw : BitcoinMalleability.SpendsWitnessPrograms u tx) :
    BitcoinSer.txid tx = BitcoinSer.txid tx' := by sorry
