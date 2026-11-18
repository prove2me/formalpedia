-- Prove2me | Theorems.Thm_ArtinKP_X_X_inner_coreLap_coreL2
-- name    : ArtinKP.X.X.inner_coreLap_coreL2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:52.420689+00:00
-- url     : https://prove2.me/theorems/0cf85f95-c57c-494d-bc70-5450cb39da9c
-- title:
--   ArtinKP.X.X.inner_coreLap_coreL2: ⟨Δa, b⟩ on the core of Γ is the Dirichlet form ∫ η Γ(ā, b)
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field and $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathcal O_F)$ (no further hypothesis), acting on $X$ (`ArtinKP.X.X` $F$), the product over the infinite places $w$ of $F$ (real and complex alike) of copies of hyperbolic 3-space $\{(x_w,v_w) : x_w\in\mathbb C,\ v_w>0\}$, factorwise by Möbius transformations through the complex embeddings. A function on $X$ is smooth (`ArtinKP.X.X.Smooth`) when it is $C^\infty$ in the logarithmic chart $(x_w,\log v_w)_w$ (`ArtinKP.X.chart`). The core `ArtinKP.X.X.core` $\Gamma$ is the complex vector space of the functions $\sum_{\gamma\in\Gamma}\varphi(\gamma\cdot P)$ (`ArtinKP.X.X.avg`) with $\varphi : X\to\mathbb C$ smooth and compactly supported.
--
--   `ArtinKP.X.X.L2` $\Gamma$ is $L^2$ of the orbit space $\Gamma\backslash X$ for the measure `ArtinKP.X.X.quotVol` $\Gamma$: the push-forward under the quotient map of $\eta\,d\mathrm{vol}$, where vol (`ArtinKP.X.X.vol`) is the product of the invariant measures $dx\,dv/v^3$ and $\eta$ is the chosen everywhere positive partition of unity `ArtinKP.X.X.pou` $\Gamma$. The map `ArtinKP.X.X.coreL2` $\Gamma$ is the complex-linear map sending a core function to its class in `ArtinKP.X.X.L2` $\Gamma$ (defined through `ArtinKP.X.X.l2Rep_of_mem_core`).
--
--   **In words.** For core functions $a,b$,
--   $$\big\langle [\Delta a],[b]\big\rangle_{L^2(\Gamma\backslash X)}=\int_X \eta(P)\,\Gamma(\bar a,b)(P)\,d\mathrm{vol}(P),$$
--   where $[\cdot]$ is `ArtinKP.X.X.coreL2` $\Gamma$, $\Delta a$ is `ArtinKP.X.X.coreLap` applied to $a$ (the Laplacian `ArtinKP.X.X.lap` $=\sum_w(-v_w^2(\partial^2_{\operatorname{Re}x_w}+\partial^2_{\operatorname{Im}x_w}+\partial^2_{v_w})+v_w\partial_{v_w})$), the inner product is conjugate-linear in its first argument, $\eta(P)$ is the real number given by `ArtinKP.X.X.pou` $\Gamma$ at $P$, $\bar a$ is the pointwise complex conjugate of $a$, and $\Gamma(u,w)$ (`ArtinKP.X.X.gam`) is the bilinear carré du champ $\sum_w v_w^2\big(\partial_{\operatorname{Re}x_w}u\,\partial_{\operatorname{Re}x_w}w+\partial_{\operatorname{Im}x_w}u\,\partial_{\operatorname{Im}x_w}w+\partial_{v_w}u\,\partial_{v_w}w\big)$, computed in the logarithmic chart. The integral is a Bochner integral over $X$ (so it is $0$ if the integrand is not integrable). The right-hand side is the same as in `ArtinKP.X.X.inner_coreL2_coreLap`, so together the two statements give $\langle[\Delta a],[b]\rangle=\langle[a],[\Delta b]\rangle$.
--
--   **Role in the argument.** Symmetry of the Laplacian on the core, one of the inputs to the Friedrichs extension that yields the self-adjoint Laplacian on $L^2(\Gamma\backslash X)$.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   theorem X.inner_coreLap_coreL2 (a b : X.core Γ) :
--       ⟪X.coreL2 Γ (X.coreLap Γ a), X.coreL2 Γ b⟫_ℂ =
--         ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) *
--           X.gam (fun P => conj ((a : X F → ℂ) P)) b P ∂X.vol F
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace`, `ArtinKP.X.X.core` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.pou` (definitions bundle `ArtinKPB009` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` and `ArtinKP.X.X.coreL2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.X.X.coreLap` and `ArtinKP.X.X.gam` (definitions bundle `ArtinKPB013` of this split).
--
--   **Used by.** The definitions bundle `ArtinKPB015` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB011
import Definitions.Def_ArtinKPB013

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

theorem X.inner_coreLap_coreL2 (a b : X.core Γ) :
    ⟪X.coreL2 Γ (X.coreLap Γ a), X.coreL2 Γ b⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) *
        X.gam (fun P => conj ((a : X F → ℂ) P)) b P ∂X.vol F := by
  sorry

end

end ArtinKP.X
end
