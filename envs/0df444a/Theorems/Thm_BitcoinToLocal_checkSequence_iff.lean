-- Prove2me | Theorems.Thm_BitcoinToLocal_checkSequence_iff
-- name    : BitcoinToLocal.checkSequence_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:10:40.579782+00:00
-- url     : https://prove2.me/theorems/3cdd353c-c8bc-4e39-a6d2-f981f3d1f071
-- title:
--   CheckSequence for a 16-bit delay, in terms of the input's nSequence
-- statement:
--   For $0 \le {\rm delay} < 2^{16}$: `checkSequence tx nIn delay = true` iff the transaction version is at least 2, the input's `nSequence` has no disable bit, its masked value (type flag and low 16 bits) is below the type flag (block-based), and the delay is at most that masked value. `BIP68`/`BIP112` as `GenericTransactionSignatureChecker::CheckSequence` implements them, specialised to a block-count delay.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.checkSequence_iff (tx : BitcoinSer.Tx) (nIn : Nat) (delay : Int) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16) :
    BitcoinSig.checkSequence tx nIn delay = true ↔
      2 ≤ tx.version ∧
      BitcoinToLocal.inputSequence tx nIn &&& BitcoinSig.SEQUENCE_LOCKTIME_DISABLE_FLAG = 0 ∧
      BitcoinToLocal.inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) <
        BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ∧
      delay.toNat ≤ BitcoinToLocal.inputSequence tx nIn &&& (BitcoinSig.SEQUENCE_LOCKTIME_TYPE_FLAG ||| BitcoinSig.SEQUENCE_LOCKTIME_MASK) := by sorry
