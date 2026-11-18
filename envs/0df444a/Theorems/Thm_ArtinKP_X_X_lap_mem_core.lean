-- Prove2me | Theorems.Thm_ArtinKP_X_X_lap_mem_core
-- name    : ArtinKP.X.X.lap_mem_core
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:20:10.751991+00:00
-- url     : https://prove2.me/theorems/aa36c333-5383-48ec-a736-09f2e0b797a5
-- title:
--   ArtinKP.X.X.lap_mem_core: the Laplacian maps the core of Γ into itself
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field and $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathcal O_F)$ (no further hypothesis), acting on $X$ (`ArtinKP.X.X` $F$), the product over the infinite places $w$ of $F$ (real and complex alike) of copies of hyperbolic 3-space $\{(x_w,v_w) : x_w\in\mathbb C,\ v_w>0\}$, factorwise by Möbius transformations through the complex embeddings. A function on $X$ is smooth (`ArtinKP.X.X.Smooth`) when it is $C^\infty$ in the logarithmic chart $(x_w,\log v_w)_w$ (`ArtinKP.X.chart`). The core `ArtinKP.X.X.core` $\Gamma$ is the complex vector space of the functions $\sum_{\gamma\in\Gamma}\varphi(\gamma\cdot P)$ (`ArtinKP.X.X.avg`) with $\varphi : X\to\mathbb C$ smooth and compactly supported.
--
--   **In words.** If $w$ belongs to the core `ArtinKP.X.X.core` $\Gamma$, then so does its Laplacian $\Delta w$ (`ArtinKP.X.X.lap`). The Laplacian is computed in the logarithmic chart and equals
--   $$\Delta=\sum_w\Big(-v_w^2\big(\partial^2_{\operatorname{Re}x_w}+\partial^2_{\operatorname{Im}x_w}+\partial^2_{v_w}\big)+v_w\,\partial_{v_w}\Big),$$
--   the sum over the infinite places of the (nonnegative) hyperbolic Laplacians of the factors.
--
--   **Role in the argument.** It makes the Laplacian a linear operator of the core to itself, `ArtinKP.X.X.coreLap` $\Gamma$, the densely defined symmetric operator on $L^2(\Gamma\backslash X)$ from which the self-adjoint Laplacian is obtained.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   lemma X.lap_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.lap w ∈ X.core Γ
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.X.core` and `ArtinKP.X.X.lap` (definitions bundle `ArtinKPB006` of this split).
--
--   **Used by.** The definitions bundle `ArtinKPB013` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB006

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

lemma X.lap_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.lap w ∈ X.core Γ := by
  sorry

end

end ArtinKP.X
end
