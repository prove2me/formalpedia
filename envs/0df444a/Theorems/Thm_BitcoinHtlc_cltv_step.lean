-- Prove2me | Theorems.Thm_BitcoinHtlc_cltv_step
-- name    : BitcoinHtlc.cltv_step
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:26:06.151588+00:00
-- url     : https://prove2.me/theorems/82f7bf3d-7e39-44b2-ba03-a1219b2f22de
-- title:
--   OP_CHECKLOCKTIMEVERIFY on a serialized number passes exactly when CltvPasses holds
-- statement:
--   For a state whose stack top is `serialize expiry` with $|{\rm expiry}| < 2^{32}$: `execOp f o true OP_CHECKLOCKTIMEVERIFY s = if CltvPasses f o expiry then some s else none`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.cltv_step (f : Flags) (o : Oracle) (s : State) (expiry : Int) (rest : List Bytes)
    (hs : s.stack = BitcoinScript.serialize expiry :: rest) (hd : expiry.natAbs < 2 ^ 32) :
    BitcoinScript.execOp f o true BitcoinScript.OP_CHECKLOCKTIMEVERIFY s =
      if BitcoinHtlc.CltvPasses f o expiry then some s else none := by sorry
