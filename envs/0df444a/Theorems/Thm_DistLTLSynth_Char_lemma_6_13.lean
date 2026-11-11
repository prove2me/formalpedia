-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_6_13
-- name    : DistLTLSynth.Char.lemma_6_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:46.192885+00:00
-- url     : https://prove2.me/theorems/37ca9fb6-07ed-4139-ba16-19162893dac0
-- title:
--   Lemma 6.13 — a safety formula is realized under A iff under the closure Ā
-- statement:
--   Let $\varphi$ be a safety formula ($L(\varphi)$ a safety property) and $f$ a distributed algorithm. For every message adversary $A$,
--   $$f\text{ realizes }\varphi\text{ under }A\iff f\text{ realizes }\varphi\text{ under }\overline A,$$
--   where $\overline A$ is the closure in $\Gamma^\omega$. Liveness guarantees of an adversary do not help safety specifications.
--
--   Differences from the source:
--   - generalization: input sets X_1, X_2 are singletons (standing assumption of §6) → arbitrary finite nonempty input sets X_1, X_2; reason: the proof uses only that the first R rounds of an execution depend on the first R input signals; the singleton case X_p = Unit is an instance
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 28 (PDF 29), Lemma 6.13

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL

namespace DistLTLSynth.Char

/-- Lemma 6.13: for a safety formula `ϕ` and a distributed algorithm `f`, `f` realizes `ϕ`
under `A` iff it realizes `ϕ` under the closure `Ā` of `A` in `Γ^ω`. -/
theorem lemma_6_13 {X1 X2 Y1 Y2 : Type} [Fintype X1] [Nonempty X1] [Fintype X2] [Nonempty X2]
    [Fintype Y1] [Nonempty Y1] [Fintype Y2] [Nonempty Y2]
    (A : Set (ℕ → CommGraph)) (φ : Formula X1 X2 Y1 Y2) (hφ : φ.IsSafety)
    (f : Algorithm X1 X2 Y1 Y2) :
    FRealizes f A φ ↔ FRealizes f (closure A) φ := by sorry

end DistLTLSynth.Char
