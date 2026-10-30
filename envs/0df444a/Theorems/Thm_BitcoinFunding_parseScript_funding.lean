-- Prove2me | Theorems.Thm_BitcoinFunding_parseScript_funding
-- name    : BitcoinFunding.parseScript_funding
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:39:48.344553+00:00
-- url     : https://prove2.me/theorems/5f7b4464-f5fd-4ed5-880d-04ce4b67ed90
-- title:
--   The funding script's byte form parses to its instruction form
-- statement:
--   For keys of at most 520 bytes: `parseScript (fundingBytes pubkey1 pubkey2) = some (fundingScript pubkey1 pubkey2)`.
-- source:
--   BOLT #3, Funding Transaction Output: https://github.com/lightning/bolts/blob/master/03-transactions.md#funding-transaction-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKMULTISIG), ExecuteWitnessScript, VerifyWitnessProgram (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP141, BIP147

import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinScript
import Definitions.Def_BitcoinSig
open BitcoinFunding BitcoinHtlc
open BitcoinToLocal BitcoinSig BitcoinVerify
open BitcoinScript

theorem BitcoinFunding.parseScript_funding (pubkey1 pubkey2 : Bytes)
    (h1 : pubkey1.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) (h2 : pubkey2.length ≤ BitcoinScript.MAX_SCRIPT_ELEMENT_SIZE) :
    BitcoinSig.parseScript (BitcoinFunding.fundingBytes pubkey1 pubkey2) = some (BitcoinFunding.fundingScript pubkey1 pubkey2) := by sorry
