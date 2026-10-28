-- Prove2me | Theorems.Thm_BitcoinTaproot_sigops_budget
-- name    : BitcoinTaproot.sigops_budget
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-26T16:35:51.852877+00:00
-- url     : https://prove2.me/theorems/7cfba876-ccff-4deb-be44-6526661b9da2
-- title:
--   The validation-weight budget
-- statement:
--   An executed `OP_CHECKSIG` with a non-empty signature when fewer than 50 weight units remain is a script error (`SCRIPT_ERR_TAPSCRIPT_VALIDATION_WEIGHT`), before any key or signature is examined.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyWitnessProgram (version 1), ExecuteWitnessScript, EvalScript under SigVersion::TAPSCRIPT, EvalChecksigTapscript, CheckSchnorrSignature, SignatureHashSchnorr, ComputeTapleafHash, ComputeTapbranchHash, ComputeTaprootMerkleRoot, VerifyTaprootCommitment, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; XOnlyPubKey::CheckTapTweak, ComputeTapTweakHash, src/pubkey.cpp; secp256k1_xonly_pubkey_tweak_add_check, src/secp256k1/src/modules/extrakeys/main_impl.h; IsOpSuccess, src/script/script.cpp; BIP340, BIP341, BIP342 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Definitions.Def_BitcoinTaproot
import Definitions.Def_BitcoinScript
open BitcoinTaproot BitcoinSer BitcoinSig BitcoinVerify
open BitcoinScript hiding Bytes Byte

theorem BitcoinTaproot.sigops_budget (c : TapCtx) (ed : ExecData) (ts : TapState) (pubkey sig : Bytes) (rest : List Bytes)
    (hs : ts.st.stack = pubkey :: sig :: rest) (hsig : sig ≠ []) (hw : ts.weightLeft < BitcoinTaproot.VALIDATION_WEIGHT_PER_SIGOP_PASSED) :
    BitcoinTaproot.tapExecOp c ed true BitcoinScript.OP_CHECKSIG ts = none := by sorry
