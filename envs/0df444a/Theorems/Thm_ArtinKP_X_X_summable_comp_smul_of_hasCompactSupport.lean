-- Prove2me | Theorems.Thm_ArtinKP_X_X_summable_comp_smul_of_hasCompactSupport
-- name    : ArtinKP.X.X.summable_comp_smul_of_hasCompactSupport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:15:37.857005+00:00
-- url     : https://prove2.me/theorems/a175b20f-74a1-4a66-bba2-0f04b6941761
-- title:
--   ArtinKP.X.X.summable_comp_smul_of_hasCompactSupport: the Γ-translates of a compactly supported function are summable at every point
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **In words.** Let $F$ be a number field, $X$ (`ArtinKP.X.X` $F$) the product over the infinite places of $F$ (real and complex alike) of copies of hyperbolic 3-space $\mathbb H^3=\{(x,v): x\in\mathbb C,\ v>0\}$, with $\mathrm{SL}_2(\mathcal O_F)$ acting factorwise by Möbius transformations through the complex embeddings, and $\Gamma$ any subgroup of $\mathrm{SL}_2(\mathcal O_F)$. If $\varphi : X\to\mathbb C$ has compact support (for the product topology of $X$, each factor carrying the subspace topology from $\mathbb C\times\mathbb R$), then for every point $P\in X$ the family $\gamma\mapsto\varphi(\gamma\cdot P)$, indexed by the elements of $\Gamma$, is summable in $\mathbb C$. No continuity or measurability of $\varphi$ is assumed.
--
--   **Role in the argument.** It makes the average $\sum_{\gamma\in\Gamma}\varphi\circ\gamma$ (`ArtinKP.X.X.avg`) a genuine sum, so that the core `ArtinKP.X.X.core` $\Gamma$ of such averages of smooth compactly supported functions is a vector space: the core is the dense domain on which the Laplacian of $L^2(\Gamma\backslash X)$ is first defined.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   lemma X.summable_comp_smul_of_hasCompactSupport (Γ : Subgroup (SL(2, 𝓞 F))) {φ : X F → ℂ} (hc : HasCompactSupport φ)
--       (P : X F) : Summable fun γ : Γ => φ (γ • P)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C5.l2Rep_src`, `ArtinKP.X.X.integrable_pou_mul` and `ArtinKP.X.X.mem_core_of_support` and the definitions bundle `ArtinKPB006` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB005

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

variable {Γ : Subgroup (SL(2, 𝓞 F))}

lemma X.summable_comp_smul_of_hasCompactSupport (Γ : Subgroup (SL(2, 𝓞 F))) {φ : X F → ℂ} (hc : HasCompactSupport φ)
    (P : X F) : Summable fun γ : Γ => φ (γ • P) := by
  sorry

end

end ArtinKP.X
end
