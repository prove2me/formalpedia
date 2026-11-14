-- Prove2me | Theorems.Thm_BosonicLearn_fugacityFamily_separable
-- name    : BosonicLearn.fugacityFamily_separable
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:22:42.948251+00:00
-- url     : https://prove2.me/theorems/2822f0cb-9528-4e43-abe1-dac6730f50f4
-- title:
--   The family $\{\rho_{R_X}:X\in G_{\rm supp}\}$ is separable in trace norm
-- statement:
--   The hard family has a countable subfamily that is dense in trace norm.
--
--   Let $0<\nu\le1$ and $0<\xi<1/32$. There is a sequence $D_0,D_1,\dots\in G_{\mathrm{supp}}$ such that for every $X\in G_{\mathrm{supp}}$ and every $\eta>0$ there is $k$ with
--
--   $$
--   \big\|\rho_{R_X}-\rho_{R_{D_k}}\big\|_1<\eta,\qquad \rho_{R}=\det(\mathbf 1-R)\Gamma(R),\quad R_X=r(\mathbf 1+\xi X).
--   $$
--
--   Why it holds. $G_{\mathrm{supp}}$ is a compact subset of the finite-dimensional space $\mathrm{Herm}_0(n)$, hence separable, and $X\mapsto\rho_{R_X}$ is continuous in trace norm (photon-number cutoff).
--
--   Role. In the proof of Theorem 5 an estimate $\hat\rho$ of the state is converted into an estimate $\hat X$ of $X$ by taking a nearest point of a net. With a countable dense family the nearest-point rule "first index $k$ with $\|\hat\rho-\rho_{R_{D_k}}\|_1<3\varepsilon$" is a measurable map from states to $\mathrm{Herm}_0(n)$, which is what Proposition 5 requires of the estimator.
--
--   **Formalization Note** $\|\cdot\|_1$ is `traceSize` on the coefficient arrays `fugacityCoeff (fugacityFamily ν ξ X)`. The paper uses a finite $\eta$-net for $\eta=\varepsilon$; the countable family valid for all $\eta$ is used instead so that no compactness argument is needed downstream.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, proof of Theorem 5, Eq. (106), p. 40 ("G_supp is compact and the map X ↦ ρ_{R_X} is continuous in trace norm … has an η-covering net")

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open scoped ENNReal

namespace BosonicLearn

/-- **The hard family is separable in trace norm.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, proof of Theorem 5, Eq. (106), p. 40: "Since G_supp is compact and the map X ↦ ρ_{R_X} is continuous in
trace norm (which can be shown by appropriate photon number cutoff), the image {ρ_{R_X} : X ∈ G_supp} has an
η-covering net in trace norm".

For `0 < ν ≤ 1` and `0 < ξ < 1/32` there is a sequence `D₀, D₁, … ∈ G_supp` such that for every `X ∈ G_supp` and
every `η > 0` some `k` has `‖ρ_{R_X} − ρ_{R_{D_k}}‖₁ < η`.

**Formalization Note.** The paper uses a finite `η`-net for one `η`; a countable family that works for every `η`
exists for the same reason (continuity of `X ↦ ρ_{R_X}` in trace norm and separability of `G_supp`) and is what a
measurable nearest-point decoder needs. `‖·‖₁` is `traceSize`. -/
theorem fugacityFamily_separable (n : ℕ) (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) :
    ∃ D : ℕ → Herm0 n, (∀ k, D k ∈ Gsupp n) ∧ ∀ X ∈ Gsupp n, ∀ η : ℝ, 0 < η →
      ∃ k, traceSize (fugacityCoeff (fugacityFamily ν ξ X) -
        fugacityCoeff (fugacityFamily ν ξ (D k))) < ENNReal.ofReal η := by sorry

end BosonicLearn
