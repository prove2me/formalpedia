-- Prove2me | Theorems.Thm_ArtinKP_X_exists_isPOU_forall_pos
-- name    : ArtinKP.X.exists_isPOU_forall_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:20:55.113613+00:00
-- url     : https://prove2.me/theorems/5c9b810a-9b3e-4c5d-940f-db4afeb6b65c
-- title:
--   ArtinKP.X.exists_isPOU_forall_pos: every subgroup of SL₂(𝓞_F) has an everywhere positive partition of unity on X
-- statement:
--   A named statement of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **In words.** Let $F$ be a number field and let $X$ (`ArtinKP.X.X` $F$) be the product, over the infinite places $w$ of $F$ (real and complex alike), of copies of hyperbolic 3-space $\mathbb H^3=\{(x,v)\in\mathbb C\times\mathbb R : v>0\}$ (`ArtinKP.X.H3`). The group $\mathrm{SL}_2(\mathcal O_F)$ acts on $X$ factorwise: an element is mapped into $\mathrm{SL}_2(\mathbb C)$ by the complex embedding attached to $w$, which acts on the $w$-th factor by the Möbius action $g\cdot(x,v)=\big(((ax+b)\overline{(cx+d)}+a\bar c v^2)/D,\ v/D\big)$, $D=|cx+d|^2+|c|^2v^2$. The statement says: for every subgroup $\Gamma$ of $\mathrm{SL}_2(\mathcal O_F)$ there is a function $\eta : X\to[0,\infty]$ that is a partition of unity for $\Gamma$ in the sense of `ArtinKP.X.IsPOU` (it is measurable, and $\sum_{\gamma\in\Gamma}\eta(\gamma\cdot P)=1$ for every point $P$, the sum taken in $[0,\infty]$; the sum runs over the elements of $\Gamma$, so when $-1\in\Gamma$, which acts trivially on $X$, every orbit point is counted at least twice) and that is strictly positive at every point of $X$.
--
--   No hypothesis is made on $\Gamma$: the trivial subgroup and subgroups of infinite index are included.
--
--   **Role in the argument.** The development never builds a fundamental domain. Integrals over $\Gamma\backslash X$ are integrals over $X$ against a partition of unity, and the quotient measure is the push-forward of $\eta\,d\mathrm{vol}$; the positivity is what makes a continuous invariant function that vanishes almost everywhere on the quotient vanish identically. The partition of unity used everywhere, `ArtinKP.X.X.pou`, is chosen from this statement.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal`, `open MeasureTheory Set NumberField`):
--
--   ```lean
--   theorem exists_isPOU_forall_pos (Γ : Subgroup (SL(2, 𝓞 F))) :
--       ∃ η : X F → ℝ≥0∞, IsPOU Γ η ∧ ∀ P, 0 < η P
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.IsPOU` (definitions bundle `ArtinKPB008` of this split).
--
--   **Used by.** The proof of `ArtinKP.X.X.isPOU_pou` and the definitions bundle `ArtinKPB009` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB008

section

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem exists_isPOU_forall_pos (Γ : Subgroup (SL(2, 𝓞 F))) :
    ∃ η : X F → ℝ≥0∞, IsPOU Γ η ∧ ∀ P, 0 < η P := by
  sorry

end

end ArtinKP.X
end
