-- Prove2me | Theorems.Thm_BitcoinHtlc_cltv_concrete
-- name    : BitcoinHtlc.cltv_concrete
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:29:11.774067+00:00
-- url     : https://prove2.me/theorems/22958a48-b494-46a9-8121-9b7e16d7be75
-- title:
--   With CLTV active, the operand check is the transaction's CheckLockTime
-- statement:
--   For `f.cltv = true` and $0 \le {\rm expiry}$: `CltvPasses f (legacyOracle sf tx nIn amount v sc) expiry ↔ checkLockTime tx nIn expiry = true`.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.cltv_concrete (f : Flags) (sf : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : Bytes) (expiry : Int) (hcltv : f.cltv = true) (h0 : 0 ≤ expiry) :
    BitcoinHtlc.CltvPasses f (BitcoinSig.legacyOracle sf tx nIn amount v sc) expiry ↔
      BitcoinSig.checkLockTime tx nIn expiry = true := by sorry
