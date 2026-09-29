-- Prove2me | Theorems.Thm_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq
-- name    : CuspForm.exists_eq_sum_smul_slash_of_forall_slash_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/45784482-281c-5699-bf60-1464dac79ddf
-- title:
--   Slash-invariant combinations of rational slashes are cusp forms
-- statement:
--   Let $M$ and $N$ be natural numbers with $M$ nonzero, let $g$ be a cusp form of weight $2$ on $\Gamma_0(M) \le \mathrm{SL}_2(\mathbb{Z})$, let $\iota$ be a finite type, and let $c : \iota \to \mathbb{C}$ be coefficients and $\beta : \iota \to \mathrm{GL}_2(\mathbb{Q})$ a family of invertible rational matrices. Let $F : \mathcal{H} \to \mathbb{C}$ be a function on the upper half-plane which is assumed to be the finite linear combination $F = \sum_{i} c_i \, \bigl(g \mid_2 \beta_i^{\mathbb{R}}\bigr)$, where $\beta_i^{\mathbb{R}} \in \mathrm{GL}_2(\mathbb{R})$ is the image of $\beta_i$ under the entrywise map induced by $\mathbb{Q} \hookrightarrow \mathbb{R}$ and $\mid_2$ is Mathlib's weight-$2$ slash action of $\mathrm{GL}_2(\mathbb{R})$. Assume further that $F \mid_2 \gamma = F$ for every $\gamma$ in the image of $\Gamma_0(N)$ under the homomorphism $\mathrm{SL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{R})$, i.e. for every element of $\Gamma_0(N)$ regarded inside $\mathrm{GL}_2(\mathbb{R})$. The conclusion is that there exists a cusp form $h$ of weight $2$ on $\Gamma_0(N)$ whose underlying function equals $F$.
--
--   This is the standard descent step which recognises a $\Gamma_0(N)$-invariant finite combination of rational translates of a weight-two cusp form of some level $M$ as itself a weight-two cusp form of level $N$, the shape in which Hecke translates and oldform contributions arise. It is used in the treatment of normalised eigenforms and their adelic lifts, where a function known to lie in the span of such slashes and to be fixed by $\Gamma_0(N)$ must be promoted to an honest element of $S_2(\Gamma_0(N))$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm

theorem CuspForm.exists_eq_sum_smul_slash_of_forall_slash_eq
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N),
      F ∣[(2 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ⇑h = F := by sorry
