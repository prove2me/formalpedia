-- Prove2me | Theorems.Thm_ArtinKP_X_X_inner_coreL2_coreLap_self
-- name    : ArtinKP.X.X.inner_coreL2_coreLap_self
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:33:31.838197+00:00
-- url     : https://prove2.me/theorems/acbfd414-256f-4804-ac19-18e956b87563
-- title:
--   ArtinKP.X.X.inner_coreL2_coreLap_self: ⟨a, Δa⟩ on the core of Γ is the Dirichlet energy ∫ η |∇a|², a real number
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field and $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathcal O_F)$ (no further hypothesis), acting on $X$ (`ArtinKP.X.X` $F$), the product over the infinite places $w$ of $F$ (real and complex alike) of copies of hyperbolic 3-space $\{(x_w,v_w) : x_w\in\mathbb C,\ v_w>0\}$, factorwise by Möbius transformations through the complex embeddings. A function on $X$ is smooth (`ArtinKP.X.X.Smooth`) when it is $C^\infty$ in the logarithmic chart $(x_w,\log v_w)_w$ (`ArtinKP.X.chart`). The core `ArtinKP.X.X.core` $\Gamma$ is the complex vector space of the functions $\sum_{\gamma\in\Gamma}\varphi(\gamma\cdot P)$ (`ArtinKP.X.X.avg`) with $\varphi : X\to\mathbb C$ smooth and compactly supported.
--
--   `ArtinKP.X.X.L2` $\Gamma$ is $L^2$ of the orbit space $\Gamma\backslash X$ for the measure `ArtinKP.X.X.quotVol` $\Gamma$: the push-forward under the quotient map of $\eta\,d\mathrm{vol}$, where vol (`ArtinKP.X.X.vol`) is the product of the invariant measures $dx\,dv/v^3$ and $\eta$ is the chosen everywhere positive partition of unity `ArtinKP.X.X.pou` $\Gamma$. The map `ArtinKP.X.X.coreL2` $\Gamma$ is the complex-linear map sending a core function to its class in `ArtinKP.X.X.L2` $\Gamma$ (defined through `ArtinKP.X.X.l2Rep_of_mem_core`).
--
--   **In words.** For a core function $a$,
--   $$\big\langle [a],[\Delta a]\big\rangle_{L^2(\Gamma\backslash X)}=\int_X \eta(P)\,|\nabla a|^2(P)\,d\mathrm{vol}(P),$$
--   the right-hand side being a real Bochner integral over $X$ (so $0$ if the integrand is not integrable), viewed as a complex number. Here $[\cdot]$ is `ArtinKP.X.X.coreL2` $\Gamma$, $\Delta a$ is `ArtinKP.X.X.coreLap` applied to $a$, the inner product is conjugate-linear in its first argument, $\eta(P)$ is the real number given by `ArtinKP.X.X.pou` $\Gamma$ at $P$, and $|\nabla a|^2$ (`ArtinKP.X.X.grad2`) is the hyperbolic squared gradient $\sum_w v_w^2\big(|\partial_{\operatorname{Re}x_w}a|^2+|\partial_{\operatorname{Im}x_w}a|^2+|\partial_{v_w}a|^2\big)$, computed in the logarithmic chart.
--
--   **Role in the argument.** It shows that the Laplacian on the core is a nonnegative operator, with the Dirichlet energy as its quadratic form; this is what the Friedrichs extension and the energy space $H^1(\Gamma\backslash X)$ are built on.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   theorem X.inner_coreL2_coreLap_self (a : X.core Γ) :
--       ⟪X.coreL2 Γ a, X.coreL2 Γ (X.coreLap Γ a)⟫_ℂ =
--         ((∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F : ℝ) : ℂ)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace`, `ArtinKP.X.X.core` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.pou` (definitions bundle `ArtinKPB009` of this split); `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` and `ArtinKP.X.X.coreL2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.X.X.coreLap` (definitions bundle `ArtinKPB013` of this split); `ArtinKP.X.X.grad2` (definitions bundle `ArtinKPB014` of this split).
--
--   **Used by.** The proofs of `ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff` and `ArtinKP.X.X.ims` and the definitions bundle `ArtinKPB015` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB011
import Definitions.Def_ArtinKPB013
import Definitions.Def_ArtinKPB014

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

theorem X.inner_coreL2_coreLap_self (a : X.core Γ) :
    ⟪X.coreL2 Γ a, X.coreL2 Γ (X.coreLap Γ a)⟫_ℂ =
      ((∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F : ℝ) : ℂ) := by
  sorry

end

end ArtinKP.X
end
