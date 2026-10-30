-- Prove2me | Theorems.Thm_BitcoinHtlc_multisig_two
-- name    : BitcoinHtlc.multisig_two
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T17:26:18.554615+00:00
-- url     : https://prove2.me/theorems/9d7aedef-4b0c-43d7-9f70-4c92b181213b
-- title:
--   A 2-of-2 CHECKMULTISIG loop passes iff each signature matches its key in order
-- statement:
--   `multisigLoop o [s₁, s₂] [k₁, k₂] = some true ↔ o.checkSig s₁ k₁ = some true ∧ o.checkSig s₂ k₂ = some true`. With two signatures and two keys the interpreter's matching loop cannot skip a key.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinScript
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinHtlc.multisig_two (o : Oracle) (s1 s2 k1 k2 : Bytes) :
    BitcoinScript.multisigLoop o [s1, s2] [k1, k2] = some true ↔
      o.checkSig s1 k1 = some true ∧ o.checkSig s2 k2 = some true := by sorry
