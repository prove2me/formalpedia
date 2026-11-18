-- Prove2me | Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
-- name    : ArtinKP.X.X.l2Rep_of_mem_core
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:06.830251+00:00
-- url     : https://prove2.me/theorems/532838a8-1433-423b-8b38-16ba7588aae6
-- title:
--   ArtinKP.X.X.l2Rep_of_mem_core: every core function of Γ is a measurable Γ-invariant function, square integrable on Γ\X
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Setting.** $F$ is a number field and $\Gamma$ a subgroup of $\mathrm{SL}_2(\mathcal O_F)$ (no further hypothesis), acting on $X$ (`ArtinKP.X.X` $F$), the product over the infinite places $w$ of $F$ (real and complex alike) of copies of hyperbolic 3-space $\{(x_w,v_w) : x_w\in\mathbb C,\ v_w>0\}$, factorwise by Möbius transformations through the complex embeddings. A function on $X$ is smooth (`ArtinKP.X.X.Smooth`) when it is $C^\infty$ in the logarithmic chart $(x_w,\log v_w)_w$ (`ArtinKP.X.chart`). The core `ArtinKP.X.X.core` $\Gamma$ is the complex vector space of the functions $\sum_{\gamma\in\Gamma}\varphi(\gamma\cdot P)$ (`ArtinKP.X.X.avg`) with $\varphi : X\to\mathbb C$ smooth and compactly supported.
--
--   **In words.** Every function $w$ in the core `ArtinKP.X.X.core` $\Gamma$ satisfies `ArtinKP.X.X.L2Rep` $\Gamma$: it is measurable, it is $\Gamma$-invariant ($w(\gamma\cdot P)=w(P)$ for all $\gamma\in\Gamma$ and $P\in X$), and the function it induces on the orbit space $\Gamma\backslash X$ (its value at a chosen representative of each orbit) is square integrable for the quotient measure `ArtinKP.X.X.quotVol` $\Gamma$, the push-forward of $\eta\,d\mathrm{vol}$ with $\eta$ = `ArtinKP.X.X.pou` $\Gamma$ and vol the product of the measures $dx\,dv/v^3$.
--
--   **Role in the argument.** It gives every core function a class in $L^2(\Gamma\backslash X)$: the map `ArtinKP.X.X.coreL2` $\Gamma$ from the core to `ArtinKP.X.X.L2` $\Gamma$ is defined through it.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   lemma X.l2Rep_of_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.L2Rep Γ w
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.X.core` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.L2Rep` (definitions bundle `ArtinKPB010` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C5.l2Rep_src`, `ArtinKP.X.X.coreL2_injective`, `ArtinKP.X.X.dense_range_coreL2`, `ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff`, `ArtinKP.X.X.ims`, `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreLap_coreL2` and `ArtinKP.X.X.inner_coreLap_eq` and the definitions bundle `ArtinKPB011` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB010

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

lemma X.l2Rep_of_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.L2Rep Γ w := by
  sorry

end

end ArtinKP.X
end
