-- Prove2me | Theorems.Thm_BitcoinToLocal_csv_concrete
-- name    : BitcoinToLocal.csv_concrete
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:10:30.895888+00:00
-- url     : https://prove2.me/theorems/c54f02d6-543b-40c1-8fbf-55d059164167
-- title:
--   With CSV active and a 16-bit delay, the operand check is the transaction's CheckSequence
-- statement:
--   For `f.csv = true` and $0 \le {\rm delay} < 2^{16}$: `CsvPasses f (legacyOracle sf tx nIn amount v sc) delay ↔ checkSequence tx nIn delay = true`. A 16-bit delay carries no disable bit.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSig
import Definitions.Def_BitcoinSer
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.csv_concrete (f : Flags) (sf : BitcoinSig.SigFlags) (tx : BitcoinSer.Tx) (nIn : Nat) (amount : Int)
    (v : BitcoinSig.SigVersion) (sc : Bytes) (delay : Int) (hcsv : f.csv = true) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16) :
    BitcoinToLocal.CsvPasses f (BitcoinSig.legacyOracle sf tx nIn amount v sc) delay ↔
      BitcoinSig.checkSequence tx nIn delay = true := by sorry
