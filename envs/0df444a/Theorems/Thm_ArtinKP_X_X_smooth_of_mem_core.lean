-- Prove2me | Theorems.Thm_ArtinKP_X_X_smooth_of_mem_core
-- name    : ArtinKP.X.X.smooth_of_mem_core
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:20:08.593534+00:00
-- url     : https://prove2.me/theorems/039a8b3d-5d0d-4b70-8e75-c1c58fa3870e
-- title:
--   ArtinKP.X.X.smooth_of_mem_core: every function of the core of Γ is smooth on X
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field and $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathcal O_F)$ (no further hypothesis), acting on $X$ (`ArtinKP.X.X` $F$), the product over the infinite places $w$ of $F$ (real and complex alike) of copies of hyperbolic 3-space $\{(x_w,v_w) : x_w\in\mathbb C,\ v_w>0\}$, factorwise by Möbius transformations through the complex embeddings. A function on $X$ is smooth (`ArtinKP.X.X.Smooth`) when it is $C^\infty$ in the logarithmic chart $(x_w,\log v_w)_w$ (`ArtinKP.X.chart`). The core `ArtinKP.X.X.core` $\Gamma$ is the complex vector space of the functions $\sum_{\gamma\in\Gamma}\varphi(\gamma\cdot P)$ (`ArtinKP.X.X.avg`) with $\varphi : X\to\mathbb C$ smooth and compactly supported.
--
--   **In words.** Every function $w : X\to\mathbb C$ that belongs to the core `ArtinKP.X.X.core` $\Gamma$ is smooth in the sense of `ArtinKP.X.X.Smooth`: its pull-back along the logarithmic chart is $C^\infty$ (`ContDiff` of order $\infty$ over $\mathbb R$, not real-analytic).
--
--   **Role in the argument.** The core is the domain on which the Laplacian of $L^2(\Gamma\backslash X)$ is defined before it is extended to a self-adjoint operator; smoothness is what lets the Laplacian (`ArtinKP.X.X.lap`) and Green's identity be applied to core functions, and it enters the definition of the Laplacian on the core, `ArtinKP.X.X.coreLap`.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   lemma X.smooth_of_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.Smooth w
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.X.Smooth` and `ArtinKP.X.X.core` (definitions bundle `ArtinKPB006` of this split).
--
--   **Used by.** The proofs of `ArtinKP.X.X.coreL2_injective`, `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreLap_coreL2` and `ArtinKP.X.X.l2Rep_of_mem_core` and the definitions bundle `ArtinKPB013` of this split import it.
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

lemma X.smooth_of_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.Smooth w := by
  sorry

end

end ArtinKP.X
end
