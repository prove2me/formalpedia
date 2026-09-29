-- Prove2me | Theorems.Thm_CohCarrier_heckeT_iDeg_q_eq_smul_r
-- name    : CohCarrier.heckeT_iDeg_q_eq_smul_r
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/37e34fc6-3f1e-5b37-95e5-7f871246aaad
-- title:
--   U_qι_q^* = q ι₁^* at level Γ_{H_r}(Nq)
-- statement:
--   Fix natural numbers $N$ and $q$ with $q \neq 0$ and $Nq \neq 0$, and an additive commutative group $A$. Let $r$ divide $N$ with $4 \le r$, let $H_r \le (\mathbb{Z}/N)^{\times}$ be the subgroup characterised by the condition that a unit $u$ lies in $H_r$ exactly when its image under the reduction $\mathbb{Z}/N \to \mathbb{Z}/r$ is $1$, and let $H_r' \le (\mathbb{Z}/Nq)^{\times}$ be characterised likewise by the reduction $\mathbb{Z}/Nq \to \mathbb{Z}/r$ coming from $r \mid N \mid Nq$. Assume `LevelLE N (N * q) Hr Hr' 1` and `LevelLE N (N * q) Hr Hr' q`, i.e. in both cases $N \mid Nq$ and reduction $(\mathbb{Z}/Nq)^{\times} \to (\mathbb{Z}/N)^{\times}$ carries $H_r'$ into $H_r$, together with the divisibility $1 \mid Nq/N$, respectively $q \mid Nq/N$. Let $\varphi$ be an element of `H1 N Hr A`, that is, a homomorphism from the additive form of the subgroup `GammaH N Hr` of $\mathrm{SL}_2(\mathbb{Z})$ (the image in $\mathrm{SL}_2(\mathbb{Z})$ of those elements of $\Gamma_0(N)$ whose associated unit lies in $H_r$) to $A$. Then applying the transfer-defined operator `heckeT` at $q$ and level $(Nq, H_r')$ to the degeneracy pullback `iDeg'` of $\varphi$ along the $q$-conjugation embedding $\mathrm{GammaH}(Nq,H_r') \to \mathrm{GammaH}(N,H_r)$ gives $q$ times the degeneracy pullback of $\varphi$ along the corresponding embedding for $d = 1$.
--
--   This is the relation $U_q \iota_q^* = q\,\iota_1^*$ between the Hecke operator at $q$ and the two degeneracy maps from level $N$ to level $Nq$, here for the level structures $\Gamma_{H_r}$ with $H_r$ the units congruent to $1$ modulo $r$, and with cohomology replaced by homomorphisms out of the group itself. It is used in the construction of refinements of corner data and of the level-raising/degeneracy comparisons at level $Nq$ in the Hecke-algebra local analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_iDeg_q_eq_smul_r.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_iDeg_q_eq_smul_r {N q : ℕ} [NeZero q] {A : Type} [AddCommGroup A] [NeZero (N * q)]
    (r : ℕ) (hrN : r ∣ N) (hr : 4 ≤ r)
    (Hr : Subgroup (ZMod N)ˣ)
    (hHr : ∀ u : (ZMod N)ˣ, u ∈ Hr ↔ ZMod.castHom hrN (ZMod r) (u : ZMod N) = 1)
    (Hr' : Subgroup (ZMod (N * q))ˣ)
    (hHr' : ∀ u : (ZMod (N * q))ˣ,
      u ∈ Hr' ↔ ZMod.castHom (dvd_mul_of_dvd_left hrN (q)) (ZMod r) (u : ZMod (N * q)) = 1)
    (h₁ : LevelLE N (N * q) Hr Hr' 1)
    (hq : LevelLE N (N * q) Hr Hr' q)
    (φ : H1 N Hr A) :
    heckeT (N * q) Hr' q A (iDeg' N (N * q) Hr Hr' q A hq φ)
      = q • iDeg' N (N * q) Hr Hr' 1 A h₁ φ := by sorry
