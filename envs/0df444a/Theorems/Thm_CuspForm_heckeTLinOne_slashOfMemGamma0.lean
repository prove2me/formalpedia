-- Prove2me | Theorems.Thm_CuspForm_heckeTLinOne_slashOfMemGamma0
-- name    : CuspForm.heckeTLinOne_slashOfMemGamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/5ca68639-297a-5f0d-b52c-947ef4f5c9f5
-- title:
--   T_ℓ commutes with the Γ₀(M)-action on S_k(Γ₁(M))
-- statement:
--   Let $M$ and $k$ be integers with $M \ge 0$, let $\ell$ be a prime with $\ell \nmid M$, let $\gamma \in SL(2,\mathbb{Z})$ lie in $\Gamma_0(M)$, and let $f$ be a cusp form of weight $k$ for $\Gamma_1(M)$. Two operations on such cusp forms are involved. First, [`CuspForm.slashOfMemGamma0 M k hγ`](def/CuspForm_Gamma1HeckeOperators.html#L535) sends $f$ to the cusp form for $\Gamma_1(M)$ whose underlying function is $f \mid_k \gamma$ (the image of $\gamma$ in $GL_2^+(\mathbb{R})$ acting by the weight-$k$ slash); this is well defined because $\gamma$ normalises $\Gamma_1(M)$. Second, [`CuspForm.heckeTLinOne k hℓ hℓM`](def/CuspForm_Gamma1HeckeOperators.html#L652) is the $\mathbb{C}$-linear operator sending $f$ to the cusp form with underlying function $\mathrm{heckeU}\,k\,\ell\,f + (\langle \ell \rangle f) \mid_k \mathrm{heckeDiagMatrix}\,\ell$, where $\langle \ell \rangle =$ `diamondLinOne M k ℓ`. The assertion is that these two commute: applying `heckeTLinOne` to $f \mid_k \gamma$ gives the same cusp form as slashing $\mathrm{heckeTLinOne}(f)$ by $\gamma$.
--
--   This is the standard compatibility of the Hecke operator $T_\ell$, for $\ell$ prime to the level, with the action of $\Gamma_0(M)/\Gamma_1(M)$ on $S_k(\Gamma_1(M))$, i.e. with the diamond operators. It underlies the commuting-family arguments used in the Deligne–Serre style results on weight-one Hecke eigenforms and in the computation relating torsion on a modular curve to the characteristic polynomial of `heckeTLinOne`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeTLinOne_slashOfMemGamma0.lean

import Mathlib
import Definitions.Def_CuspForm_Gamma1HeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.heckeTLinOne_slashOfMemGamma0
    {M : ℕ} (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Gamma1 M) k) :
    CuspForm.heckeTLinOne k hℓ hℓM (CuspForm.slashOfMemGamma0 M k hγ f) =
      CuspForm.slashOfMemGamma0 M k hγ (CuspForm.heckeTLinOne k hℓ hℓM f) := by sorry
