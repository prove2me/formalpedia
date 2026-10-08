-- Prove2me | Theorems.Thm_ConnesGreen_canonical_negative_tests_after_half_cut
-- name    : ConnesGreen.canonical_negative_tests_after_half_cut
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:52:11.263282+00:00
-- url     : https://prove2.me/theorems/6230f7b9-365c-4976-ad72-c779b8e9ef1f
-- title:
--   Original selected-negative tests beyond an inner cutoff retain the complete tail balance
-- statement:
--   Suppose $c$ characterizes the successful windows of the original finite packet $S$. For every positive $T>c$, we prove existence of an ORIGINAL supported test $g$ such that, with $x=\mathrm{sourceEmbed}_T(\mathrm{problemOneL}(g))$,
--   $$\|P_T^*x\|^2-\|M_{T,S}^*x\|^2<0,\qquad
--   \|B_{T,S}^*x\|^2<-\operatorname{Re}W(g*\mathrm{starInv}(g)).$$
--   The accepted exact equivalence between the original Picard half-bound and nonnegativity on all original supported tests makes a failed window supply a selected-negative test. The complete original tail is retained: the closed negative-analysis partition gives
--   $$\|N_T^*x\|^2=\|M_{T,S}^*x\|^2+\|B_{T,S}^*x\|^2.$$
--   Original actor-column summability and Cauchy-Schwarz justify these convergent squared analysis sums. Accepted full signed actor arithmetic then identifies
--   $$\operatorname{Re}W(g*\mathrm{starInv}(g))+\|B_{T,S}^*x\|^2
--   =\|P_T^*x\|^2-\|M_{T,S}^*x\|^2<0.$$
--   This proves the asserted strict full-background balance. The cutoff characterization is an explicit premise of this reduction and is the finite branch supplied by the separate unconditional dichotomy. All original actor, carrier, actual-zero, analytic multiplicity and reflected-pair normalizations are retained. The result is not an unconditional proof that a given packet has a finite cutoff, nor a critical-endpoint jump budget or RH proof.
-- source:
--   monocap-tech/weil at e6d17e3f8533cdffc6af82283874365e7d869f8e; WeilDefect/Connes/HalfWindowClassification.lean (new additive module), using unchanged original CriticalWindowBoundary and actor definitions.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_negative_tests_after_half_cut (S : Finset CriticalZeros)
    (c : ℝ) (hcut : (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ c))
    (T : ℝ) (hT : 0 < T) (hcT : c < T) :
    ∃ g : ℝ → ℂ, SupportedTest T g ∧
      ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < 0 ∧
      ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 <
        -(weilDistribution (conv g (starInv g))).re := by sorry
