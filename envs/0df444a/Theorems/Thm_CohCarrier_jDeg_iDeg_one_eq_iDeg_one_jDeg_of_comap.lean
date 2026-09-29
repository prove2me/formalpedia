-- Prove2me | Theorems.Thm_CohCarrier_jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap
-- name    : CohCarrier.jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/96d5187c-25ec-5a98-ac84-27610df02029
-- title:
--   Degeneracy transfer commutes with restriction to Γ_H
-- statement:
--   Fix non-zero natural numbers $M$, $M'$ and $d$, subgroups $H \le (\mathbb{Z}/M)^\times$ and $H' \le (\mathbb{Z}/M')^\times$, and write $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the matrices of $\Gamma_0(M)$ whose image under the diagonal unit character lies in $H$, so that [`CohCarrier.H1 M H A`](def/CohCarrier_Level.html#L162) is the group of homomorphisms $\Gamma_H(M) \to A$ for an abelian group $A$. Assume: [`CohCarrier.LevelLE M M' H H' d`](def/CohCarrier_Level.html#L330), i.e. $M \mid M'$, $d \mid M'/M$ and reduction $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$ carries $H'$ into $H$; the same data with $H = H' = \top$; and the two trivial level relations `LevelLE M M ⊤ H 1` and `LevelLE M' M' ⊤ H' 1` used to form the inclusions $\Gamma_H(M) \hookrightarrow \Gamma_0(M)$ and $\Gamma_{H'}(M') \hookrightarrow \Gamma_0(M')$. Assume further that $H'$ is the full preimage of $H$: for every $u \in (\mathbb{Z}/M')^\times$, $u \in H'$ if and only if its reduction lies in $H$. Then for every abelian group $A$ and every homomorphism $y \colon \Gamma_0(M') \to A$, the transfer [`CohCarrier.jDeg`](def/CohCarrier_Level.html#L482) at level $(H, H')$ — corestriction from the image of the injection $\gamma \mapsto \delta_d \gamma \delta_d^{-1}$ of $\Gamma_{H'}(M')$ into $\Gamma_H(M)$ — applied to the restriction of $y$ to $\Gamma_{H'}(M')$ equals the restriction to $\Gamma_H(M)$ of the corresponding transfer of $y$ at level $(\top, \top)$, from $\Gamma_0(M')$ to $\Gamma_0(M)$.
--
--   This is the Mackey-type compatibility of the degeneracy transfer with restriction from $\Gamma_0$-level to $\Gamma_H$-level, valid here because $H'$ is the full preimage of $H$, so that conjugation by $\mathrm{diag}(d,1)$ identifies $\Gamma_{H'}(M')$ with $\Gamma_H(M) \cap \delta_d \Gamma_0(M') \delta_d^{-1}$ and the coset spaces match. It is used in the construction of the perfect self-adjoint pairing on parabolic homomorphism groups compatible with the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.jDeg_iDeg_one_eq_iDeg_one_jDeg_of_comap
    (M M' : ℕ) [NeZero M] [NeZero M'] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ)
    (d : ℕ) [NeZero d] (h : CohCarrier.LevelLE M M' H H' d) (ht : CohCarrier.LevelLE M M' ⊤ ⊤ d)
    (h₁ : CohCarrier.LevelLE M M ⊤ H 1) (h₁' : CohCarrier.LevelLE M' M' ⊤ H' 1)
    (hH' : ∀ u : (ZMod M')ˣ, u ∈ H' ↔ ZMod.unitsMap h.dvd u ∈ H)
    (A : Type) [AddCommGroup A] (y : CohCarrier.H1 M' ⊤ A) :
    CohCarrier.jDeg M M' H H' d A h (CohCarrier.iDeg' M' M' ⊤ H' 1 A h₁' y) =
      CohCarrier.iDeg' M M ⊤ H 1 A h₁ (CohCarrier.jDeg M M' ⊤ ⊤ d A ht y) := by sorry
