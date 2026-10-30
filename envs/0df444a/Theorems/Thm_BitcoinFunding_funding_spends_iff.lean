-- Prove2me | Theorems.Thm_BitcoinFunding_funding_spends_iff
-- name    : BitcoinFunding.funding_spends_iff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:39:36.314798+00:00
-- url     : https://prove2.me/theorems/ee4e3690-1894-4931-85c6-8a05c5b18d94
-- title:
--   The funding output's single spending condition, for any witness stack
-- statement:
--   For keys of at most 520 bytes and any stack `st`: the witness-v0 success condition for `fundingScript pubkey1 pubkey2` holds iff `FundingSpend f o pubkey1 pubkey2 st`. The HTLC mission's `multisig_two` turns the loop verdict into the two signature checks in order; any other stack shape fails.
-- source:
--   BOLT #3, Funding Transaction Output: https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKMULTISIG), ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP141, BIP147

import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinVerify
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.funding_spends_iff (f : Flags) (o : Oracle) (pubkey1 pubkey2 : Bytes) (st : List Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    (∃ res, BitcoinScript.evalScript f o st (BitcoinFunding.fundingScript pubkey1 pubkey2) = some res ∧
        res.length = 1 ∧ BitcoinVerify.topTrue res = true) ↔
      BitcoinFunding.FundingSpend f o pubkey1 pubkey2 st := by sorry
