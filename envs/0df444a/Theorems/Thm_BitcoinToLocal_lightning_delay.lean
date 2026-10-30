-- Prove2me | Theorems.Thm_BitcoinToLocal_lightning_delay
-- name    : BitcoinToLocal.lightning_delay
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T15:10:52.243748+00:00
-- url     : https://prove2.me/theorems/fc09b92b-3852-4bdf-95ab-dd166514357e
-- title:
--   A commitment spend with nSequence = to_self_delay: the delayed path opens iff version ≥ 2 and nSequence ≥ delay
-- statement:
--   For $0 \le {\rm delay} < 2^{16}$ and an input whose `nSequence` is below $2^{16}$ (no flags, as Lightning sets it): `checkSequence tx nIn delay = true ↔ 2 ≤ tx.version ∧ delay ≤ inputSequence tx nIn`. Together with `p2wsh_spend` and `csv_concrete`: the local node's delayed spend is accepted exactly when its transaction is version 2 or later, sets the input's `nSequence` to at least `to_self_delay`, and carries a valid signature for the delayed key.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'to_local Output': https://github.com/lightning/bolts/blob/master/03-transactions.md#to_local-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_IF/OP_ELSE/OP_ENDIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckSequence, ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); CScript::operator<<(int64_t) (script/script.h); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinSig
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinToLocal.lightning_delay (tx : BitcoinSer.Tx) (nIn : Nat) (delay : Int) (h0 : 0 ≤ delay) (h16 : delay < 2 ^ 16)
    (hseq : BitcoinToLocal.inputSequence tx nIn < 2 ^ 16) :
    BitcoinSig.checkSequence tx nIn delay = true ↔ 2 ≤ tx.version ∧ delay.toNat ≤ BitcoinToLocal.inputSequence tx nIn := by sorry
