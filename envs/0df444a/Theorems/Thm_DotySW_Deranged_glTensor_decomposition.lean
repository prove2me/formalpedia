-- Prove2me | Theorems.Thm_DotySW_Deranged_glTensor_decomposition
-- name    : DotySW.Deranged.glTensor_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:52.520284+00:00
-- url     : https://prove2.me/theorems/a50b09a5-8560-4ff4-9987-2f6783ff23e4
-- title:
--   Eq. (16) (corrected: multiplicities C(r,t) added) — the decomposition of $\mathfrak{gl}_n^{\otimes r}$
-- statement:
--   Let $n\ge1$. Expanding $\mathfrak{gl}_n=\mathfrak{sl}_n\oplus\mathbb C$ in every slot gives
--
--   $$
--   \mathfrak{gl}_n^{\otimes r}=\bigoplus_{S\subseteq\{1,\dots,r\}}M_S,
--   $$
--
--   where $M_S$ is the span of the pure tensors with a traceless matrix in the slots of $S$ and a scalar matrix elsewhere. Moreover:
--
--   1. $M_{\{1,\dots,r\}}=\mathfrak{sl}_n^{\otimes r}$;
--   2. each $M_S$ is $\mathrm{GL}_n$-invariant;
--   3. each $M_S$ is isomorphic to $\mathfrak{sl}_n^{\otimes|S|}$ as a $\mathrm{GL}_n$-module.
--
--   Since there are $\binom rt$ subsets of size $t$, the module $\mathfrak{sl}_n^{\otimes t}$ occurs with multiplicity $\binom rt$. In particular $\mathfrak{sl}_n^{\otimes r}$ is a direct summand of $V^{r,r}$, which is what §4.2 uses.
--
--   Differences from the source:
--   - correction: $\mathfrak{gl}_n^{\otimes r}=\mathfrak{sl}_n^{\otimes r}\oplus\bigoplus_{0\le t<r}\mathfrak{sl}_n^{\otimes t}$ with each t once → an internal direct sum over the subsets S of the slots, so each t occurs with multiplicity C(r,t); reason: the printed formula is false: for n = r = 2 the left side has dimension 16 and the right side 9 + 3 + 1 = 13
--   - encoding: as an $\mathrm{SL}_n$ or $\mathrm{GL}_n$ module → invariance and intertwining for every g in `GL (Fin n) ℂ`; reason: the statement for $\mathrm{GL}_n$ contains the one for its subgroup $\mathrm{SL}_n$
--   - encoding: $V=\mathbb C^n$ with $n\ge1$ understood → the hypothesis 0 < n; reason: for n = 0 and r ≥ 1 the space is zero while $\mathfrak{sl}_n^{\otimes 0}$ is the line, so the degenerate case V = 0 is excluded
--   - encoding: $V^{r,s}=V^{\otimes r}\otimes V^{*\otimes s}$ with $\sigma$ restricted from $\mathcal B^{(n)}_{r+s}$ through $V\simeq V^*$ on $\mathrm O_n$ → vectors are functions on `Idx n (r + s)` and ρ, σ are matrices in the basis of the $e_i$ and the dual $e_i^*$, row = output, top row of a diagram = output; reason: a choice of coordinates, and $e_i\leftrightarrow e_i^*$ is the identification of p. 9
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, Eq. (16), p. 10

import Mathlib
import Definitions.Def_DotySW_Deranged_rho
import Definitions.Def_DotySW_Deranged_slTensor
import Definitions.Def_DotySW_Deranged_slotSplit

namespace DotySW.Deranged

/-- **Eq. (16), corrected: the decomposition of `gl_n^{⊗r}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, Eq. (16), p. 10.

`gl_n^{⊗r}` is the internal direct sum over the subsets `S` of the slots of the subspaces with
`sl_n` in the slots of `S` and `ℂ` elsewhere. The summand of the full set is `sl_n^{⊗r}`. Each summand
is `GL_n`-invariant and `GL_n`-isomorphic to `sl_n^{⊗|S|}`.

**Formalization Note** As printed, (16) lists `sl_n^{⊗t}` once for each `t < r`, which is false: for
`n = r = 2` the left side has dimension `16` and the right side `9 + 3 + 1 = 13`. Expanding
`gl_n = sl_n ⊕ ℂ` gives multiplicity `C(r, t)`, which is the number of subsets `S` of size `t`. The
statement for `GL_n` contains the one for `SL_n`. -/
theorem glTensor_decomposition (n r : ℕ) (hn : 0 < n) :
    DirectSum.IsInternal (fun S : Finset (Fin r) => slotSplit n r S) ∧
    slotSplit n r Finset.univ = slTensor n r ∧
    ∀ S : Finset (Fin r),
      (∀ (g : GL (Fin n) ℂ), ∀ w ∈ slotSplit n r S, (rho n r r g).mulVec w ∈ slotSplit n r S) ∧
      ∃ E : slotSplit n r S ≃ₗ[ℂ] slTensor n S.card,
        ∀ (g : GL (Fin n) ℂ) (w w' : slotSplit n r S),
          (rho n r r g).mulVec (w : Idx n (r + r) → ℂ) = w' →
            (rho n S.card S.card g).mulVec (E w : Idx n (S.card + S.card) → ℂ) = E w' := by sorry

end DotySW.Deranged
