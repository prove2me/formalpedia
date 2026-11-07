-- Prove2me | Theorems.Thm_DimFreeShadow_theorem_4_2
-- name    : DimFreeShadow.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:31.097101+00:00
-- url     : https://prove2.me/theorems/aaccd5d4-83ba-46a3-a221-ac386935e0e4
-- title:
--   Theorem 4.2 — universal recovery with the averaged rotated Petz map (JRS+18)
-- statement:
--   Let $\omega,\tau$ be density matrices on a finite-dimensional space with $\operatorname{supp}\omega\subseteq\operatorname{supp}\tau$, let $\mathcal N$ be a quantum channel with trace adjoint $\mathcal N^*$, and set $B=\mathcal N(\tau)$. On $\operatorname{supp}B$ define
--
--   $$
--   \mathcal R^{[u]}_{\tau,\mathcal N}(X)=\tau^{(1-iu)/2}\mathcal N^*\big(B^{-(1-iu)/2}XB^{-(1+iu)/2}\big)\tau^{(1+iu)/2},\qquad\mathcal R_{\tau,\mathcal N}(X)=\int_{\mathbb R}\beta_0(u)\mathcal R^{[u]}_{\tau,\mathcal N}(X)\,du.
--   $$
--
--   These maps preserve the trace of operators supported on $\operatorname{supp}B$ and agree there with channels on the full space. The averaged map satisfies
--
--   $$
--   D(\omega\|\tau)-D(\mathcal N(\omega)\|\mathcal N(\tau))\ge-2\log F\big(\omega,(\mathcal R_{\tau,\mathcal N}\circ\mathcal N)(\omega)\big),
--   $$
--
--   with natural logarithms and the root fidelity $F(\omega,\tau)=\|\sqrt\omega\sqrt\tau\|_1$.
--
--   This is the finite-dimensional specialization of Junge–Renner–Sutter–Wilde–Winter, and the external input of the paper's §4.
--
--   **Formalization Note** The rotated map is the published `P21.rotatedPetz τ N (u/2)`, which unfolds to Eq. (19), and the average is `P21.recovery τ N`. $D$ is `P21.relativeEntropy`, and $-2\log F$ is `P21.fidelityPenalty` applied to `WildeQIT.rootFidelity`.
--
--   Differences from the source:
--   - encoding: density matrices on a finite-dimensional space; a quantum channel → matrices over finite index types, with channels in finite Kraus form (QAlgorithms.IsChannel) between possibly different index types; reason: in finite dimension a completely positive trace-preserving map has a finite Kraus form
--   - encoding: on supp B; trace preserving on the supported input space; can be completed to channels on the full space → for every X with P X P = X, P the support projection of B: the trace is preserved, and some channel R has R X equal to the map at X; reason: P X P = X says that X is supported on supp B
--   - encoding: real-valued D and −2 log F → EReal-valued relativeEntropy and fidelityPenalty, the inequality written as penalty ≤ difference; reason: D is finite under the support hypotheses, and the penalty is +∞ only at F = 0
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 4.2, p.17

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_fidelity
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_WildeQIT_Recover_spectralFun

namespace DimFreeShadow

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy fidelityPenalty rotatedPetz recovery)

/-- **Theorem 4.2** (universal recovery; arXiv:2608.06345, sha256 a1a42249…, Theorem 4.2, p.17,
the finite-dimensional specialization of Junge–Renner–Sutter–Wilde–Winter 2018, Theorem 2.1 and
Remark 2.2). Let `ω, τ` be density matrices with `supp ω ⊆ supp τ`, `N` a quantum channel,
`B = N(τ)`, `P = Π_{supp B}`. The rotated maps
`R^{[u]}_{τ,N}(X) = τ^{(1−iu)/2} N*(B^{−(1−iu)/2} X B^{−(1+iu)/2}) τ^{(1+iu)/2}` (19) and the
averaged map `R_{τ,N} = ∫ β₀(u) R^{[u]}_{τ,N} du` are trace preserving on operators supported on
`supp B` and agree there with channels on the full space; and
`D(ω‖τ) − D(N(ω)‖N(τ)) ≥ −2 log F(ω, (R_{τ,N} ∘ N)(ω))`.

**Formalization Note** `R^{[u]}_{τ,N}` is the published `P21.rotatedPetz τ N (u/2)` (it unfolds
to Eq. (19): `τ^{−iu/2} τ^{1/2} N*(B^{−1/2} B^{iu/2} X B^{−iu/2} B^{−1/2}) τ^{1/2} τ^{iu/2}`, inverse
powers on the support, `N*` the Hilbert–Schmidt adjoint), and `R_{τ,N}` is `P21.recovery τ N`
(`∫ β₀(t) R^{t/2} dt`). "Supported on `supp B`" is `P X P = X`. `D` is `P21.relativeEntropy`
(natural log, `EReal`-valued; finite here because both support conditions hold); `−2 log F` is
`P21.fidelityPenalty` (`+∞` at `F = 0`) applied to the root fidelity
`WildeQIT.rootFidelity ω σ = ‖√ω √σ‖₁`. Channels are `QAlgorithms.IsChannel` (finite Kraus
form). -/
theorem theorem_4_2 {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ω τ : Matrix I I ℂ) (hω : WildeQIT.IsDensityOperator ω) (hτ : WildeQIT.IsDensityOperator τ)
    (hsupp : IsSupported ω τ) (Nch : QAlgorithms.Superop I J) (hN : QAlgorithms.IsChannel Nch) :
    (∀ u : ℝ, ∀ X : Matrix J J ℂ, WildeQIT.Recover.supportProj (Nch τ) * X * WildeQIT.Recover.supportProj (Nch τ) = X →
      (rotatedPetz τ Nch (u / 2) X).trace = X.trace) ∧
    (∀ X : Matrix J J ℂ, WildeQIT.Recover.supportProj (Nch τ) * X * WildeQIT.Recover.supportProj (Nch τ) = X →
      (recovery τ Nch X).trace = X.trace) ∧
    (∀ u : ℝ, ∃ R : QAlgorithms.Superop J I, QAlgorithms.IsChannel R ∧
      ∀ X : Matrix J J ℂ, WildeQIT.Recover.supportProj (Nch τ) * X * WildeQIT.Recover.supportProj (Nch τ) = X →
        R X = rotatedPetz τ Nch (u / 2) X) ∧
    (∃ R : QAlgorithms.Superop J I, QAlgorithms.IsChannel R ∧
      ∀ X : Matrix J J ℂ, WildeQIT.Recover.supportProj (Nch τ) * X * WildeQIT.Recover.supportProj (Nch τ) = X →
        R X = recovery τ Nch X) ∧
    fidelityPenalty (WildeQIT.rootFidelity ω (recovery τ Nch (Nch ω))) ≤
      relativeEntropy ω τ - relativeEntropy (Nch ω) (Nch τ) := by sorry

end DimFreeShadow
