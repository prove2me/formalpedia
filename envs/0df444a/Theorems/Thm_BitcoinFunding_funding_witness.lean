-- Prove2me | Theorems.Thm_BitcoinFunding_funding_witness
-- name    : BitcoinFunding.funding_witness
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:39:20.013307+00:00
-- url     : https://prove2.me/theorems/4642b528-0351-4833-b127-af0e5cc26b1b
-- title:
--   The funding script on the BOLT #3 witness
-- statement:
--   For keys of at most 520 bytes: `evalScript f o [sig2, sig1, dummy] (fundingScript pubkey1 pubkey2)` is the 2-of-2 loop's verdict `multisigLoop o [sig2, sig1] [pubkey2, pubkey1]` as a single stack element, `none` if the loop errors or if `NULLDUMMY` is on and the dummy is nonempty.
-- source:
--   BOLT #3, Funding Transaction Output: https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKMULTISIG), ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP141, BIP147

import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinScript
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.funding_witness (f : Flags) (o : Oracle) (pubkey1 pubkey2 sig1 sig2 dummy : Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinScript.evalScript f o [sig2, sig1, dummy] (BitcoinFunding.fundingScript pubkey1 pubkey2) =
      match BitcoinScript.multisigLoop o [sig2, sig1] [pubkey2, pubkey1] with
      | none => none
      | some ok => if f.nulldummy && !dummy.isEmpty then none else some [BitcoinScript.boolBytes ok] := by sorry
