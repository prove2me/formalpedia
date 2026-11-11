-- Prove2me | Theorems.Thm_DistLTLSynth_Char_lemma_6_17
-- name    : DistLTLSynth.Char.lemma_6_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:59.873657+00:00
-- url     : https://prove2.me/theorems/c2a277a8-623a-47bb-9ad8-395f7d17848f
-- title:
--   Lemma 6.17 — ϕ (safety) is realizable under Γ^ω iff the guarded ϕ̂ is realizable under A
-- statement:
--   Inputs are singletons. Let $h$ be a finite graph history such that $h^{-1}A$ is dense in $\Gamma^\omega$ (as provided by Lemma 6.16) and let $\widehat\varphi := \mathrm{Prefix}_h\to X^{|h|}\varphi$ with $\mathrm{Prefix}_h=\bigwedge_{r=1}^{|h|}X^{r-1}(\mathrm{graph}=h[r])$. For every safety formula $\varphi$,
--   $$\varphi\text{ realizable under }\Gamma^\omega\iff\widehat\varphi\text{ realizable under }A.$$
--   This transfers undecidability from the full adversary to every adversary whose image is not nowhere dense.
--
--   Differences from the source:
--   - generalization: A is ω-regular with π(A) not nowhere dense, and h is the history of Lemma 6.16 → any A and any finite graph history h with leftQuot h A dense; reason: the proof uses only density of h⁻¹A; the paper's A and h satisfy this
--   - encoding: singleton input sets → X_1 = X_2 = Unit; reason: the same instances
--   - encoding: f_p : Views_p → Y_p → f_p is a total function on the inductive type of view terms; reason: values on terms that are not process-p views never enter an execution, so the realizable specifications are the same
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), p. 29 (PDF 30), Lemma 6.17 (h and ϕ̂: p. 11, PDF 12)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL

namespace DistLTLSynth.Char

/-- Lemma 6.17: (singleton inputs) let `h` be a finite graph history such that `h⁻¹A` is
dense in `Γ^ω` (as given by Lemma 6.16). A safety formula `ϕ` is realizable under `Γ^ω` iff
the guarded formula `ϕ̂ = Prefix_h → X^{|h|} ϕ` is realizable under `A`. -/
theorem lemma_6_17 {Y1 Y2 : Type} [Fintype Y1] [Nonempty Y1] [Fintype Y2] [Nonempty Y2]
    (A : Set (ℕ → CommGraph)) (h : List CommGraph) (hdense : Dense (leftQuot h A))
    (φ : Formula Unit Unit Y1 Y2) (hφ : φ.IsSafety) :
    Realizable Set.univ φ ↔ Realizable A (hatFormula h φ) := by sorry

end DistLTLSynth.Char
