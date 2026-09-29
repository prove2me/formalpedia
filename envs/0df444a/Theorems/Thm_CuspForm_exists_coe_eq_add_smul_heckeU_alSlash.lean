-- Prove2me | Theorems.Thm_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash
-- name    : CuspForm.exists_coe_eq_add_smul_heckeU_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/b6f8c07f-2778-5252-b117-8404bdeb5fc2
-- title:
--   Trace from Γ₀(M) to Γ₀(R) of a cusp form
-- statement:
--   Let $q$ be a prime number, let $M$ be a nonzero natural number, and let $A$ be an Atkin–Lehner datum for the level $M$ at $q$: a natural number $A.R$ together with a factorisation $M = q\cdot A.R$ and integers $A.a$, $A.b$ satisfying the Bézout relation $q\,A.a - A.R\,A.b = 1$. Let $k$ be an integer and let $F$ be a cusp form of weight $k$ for the congruence subgroup $\Gamma_0(M)$. The assertion is that there exists a cusp form $G$ of weight $k$ for $\Gamma_0(A.R)$ whose underlying function on the upper half-plane is
--   $$G = F + q^{\,2-k}\cdot \mathrm{U}_q\bigl(F \mid_k A\bigr),$$
--   where $F\mid_k A$ denotes [`ModularForm.alSlash`](def/ModularForm_AtkinLehnerDatum.html#L141), the weight-$k$ slash of $F$ (in Mathlib's normalisation by $\det^{k-1}$) by the element `A.alGL` of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral matrix `A.mat` attached to the datum, and $\mathrm{U}_q$ is [`ModularForm.heckeU`](def/ModularForm_HeckeOperator.html#L93), the sum $\sum_{j=0}^{q-1} f\mid_k \begin{pmatrix}1&j\\0&q\end{pmatrix}$ of weight-$k$ slashes. The scalar $q^{\,2-k}$ is the integer power of the complex number $q$. The equality is an equality of functions $\mathbb{H}\to\mathbb{C}$, not of elements of a space of cusp forms.
--
--   This is the trace of $F$ from $\Gamma_0(M)$ to $\Gamma_0(qR)^{-}$-level $R$, i.e. the classical formula expressing $\mathrm{Tr}^{\Gamma_0(R)}_{\Gamma_0(M)}F$ as $F$ plus a multiple of $\mathrm{U}_q$ applied to the Atkin–Lehner twist of $F$, the factor $q^{2-k}$ reflecting the $\det^{k-1}$ normalisation of the slash action. It is used in the study of the $\mathrm{U}_q$-action on cusp forms of level $M$ (for instance in computing the determinant of $\mathrm{U}_q$ up to sign) and in the integrality and $q$-expansion congruence statements that feed the level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_coe_eq_add_smul_heckeU_alSlash (q : ℕ) (hq : q.Prime) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M q)
    (k : ℤ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) k) :
    ∃ G : CuspForm (CongruenceSubgroup.Gamma0 A.R) k,
      ⇑G = ⇑F + (q : ℂ) ^ (2 - k) • ModularForm.heckeU k q (ModularForm.alSlash A k ⇑F) := by sorry
