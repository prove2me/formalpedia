-- Prove2me | Theorems.Thm_DeMorganApprox_Main_lemma_5_2
-- name    : DeMorganApprox.Main.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:02:18.792172+00:00
-- url     : https://prove2.me/theorems/3f2cb409-925e-4472-8af0-0b5acac41ffe
-- title:
--   Lemma 5.2 — the leaf program computes its literal with balanced witness bound 1
-- statement:
--   Let $\ell$ be a single leaf labelled by the literal $x_i$ or $\neg x_i$. Its constructed span program has one coordinate $e_\ell$, target $e_\ell$, and one listed vector $e_\ell$ labelled by the literal. This program
--
--   1. computes the literal (it accepts exactly the inputs on which the literal is true);
--   2. is vector-form: its target and its listed vector are unit;
--   3. has balanced witness bound $S_\ell=1$;
--   4. has target the unit coordinate vector $e_\ell$.
--
--   This is the base case of the construction: every leaf terminal of a heavy chain contributes $S_\ell=1$.
--
--   Differences from the source:
--   - generalization: a formal leaf variable y_ℓ of a read-once monotone formula → an arbitrary literal xᵢ or ¬xᵢ (lit i b), its listed vector labelled pos i or neg i; reason: the positive literal of a fresh variable is the source's y_ℓ; the source substitutes the literals at the end (PDF p. 17), and the construction here carries them directly
--   - encoding: the leaf program with a fresh coordinate e_ℓ → program tie (lit i b), the constructed program of a one-leaf formula, coordinate Coord.leaf [] and column Col.lit []; reason: the leaf program is the one-leaf case of the construction; the tie rule plays no role
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Lemma 5.2, PDF p. 17 (printed p. 15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf

import Mathlib
import Definitions.Def_DeMorganApprox_Main_HeavyChains

namespace DeMorganApprox.Main

/-- Lemma 5.2, PDF p. 17 (printed p. 15). The constructed program of a single literal leaf. -/
theorem lemma_5_2 {m : ℕ} (tie : TieRule) (i : Fin m) (b : Bool) :
    (program tie (Formula.lit i b)).Computes (Formula.lit i b).eval ∧
      (program tie (Formula.lit i b)).IsVectorForm ∧
      (program tie (Formula.lit i b)).HasBalancedBound 1 ∧
      (∀ k, (program tie (Formula.lit i b)).target k = basisV (.leaf []) k.1) := by sorry

end DeMorganApprox.Main
