-- Prove2me | Theorems.Thm_BitcoinTaproot_checksig_empty
-- name    : BitcoinTaproot.checksig_empty
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:36:04.462814+00:00
-- url     : https://prove2.me/theorems/10d41d11-8e4c-499c-b0b2-0ad88bf49ef2
-- title:
--   An empty signature is a clean false
-- statement:
--   An executed `OP_CHECKSIG` with an empty signature and a 32-byte key pushes `false` (the empty vector), consumes no weight, and performs no signature check — the construction that makes `OP_CHECKSIGADD` thresholds work.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.checksig_empty (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: [] :: rest) (hpk : pubkey.length = 32) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts =
      some { ts with st := { ts.st with stack := BitcoinScript.boolBytes false :: rest } } := by sorry
