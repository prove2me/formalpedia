-- Prove2me | Theorems.Thm_CohCarrier_jDeg_iDeg_four_identities_of_dvd
-- name    : CohCarrier.jDeg_iDeg_four_identities_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/9deb90ee-e6b5-5844-b61d-415dbbb496fd
-- title:
--   Degeneracy composition table at levels N and Nq
-- statement:
--   Let $N$ and $q$ be nonzero natural numbers with $q \mid N$, and let $A$ be an abelian group. For a modulus $M$ and a subgroup $H \le (\mathbb{Z}/M)^\times$, $H^1(M,H,A)$ denotes the group of homomorphisms from $\Gamma_H(M)$ (written additively) to $A$. The two hypotheses `h1` and `hq'` are instances of `LevelLE` from level $N$ with $H = \top$ to level $Nq$ with $H' = \top$, with parameter $d = 1$ and $d = q$ respectively; `LevelLE` asserts $N \mid Nq$, that $d$ divides $(Nq)/N$, and that reduction modulo $N$ carries $H'$ into $H$ (automatic for full subgroups). For $d \in \{1,q\}$, `iDeg'` is restriction of a class along `iotaDeg`, the injection $\Gamma_{\top}(Nq) \to \Gamma_{\top}(N)$ given by conjugation by the lower-triangular scaling matrix attached to $d$, and `jDeg` is the additive transfer (corestriction) to $\Gamma_{\top}(N)$ of the class transported to the image subgroup `(iotaDeg …).range`. The conclusion is the conjunction of four identities, each for all $\varphi$: the two diagonal compositions `jDeg ∘ iDeg'` with equal parameters ($d = 1$, and $d = q$) both equal $q \bullet \varphi$; the cross composition with $d = q$ after $d = 1$ equals `heckeT N ⊤ q A φ`, the transfer to $\Gamma_{\top}(N)$ from its subgroup $\Gamma^{\mathrm{up}}_{\top}(N,q)$ of $\varphi$ restricted along `conjL` (conjugation by the upper matrix attached to $q$); and the cross composition with $d = 1$ after $d = q$ equals `heckeTlower N ⊤ q A φ`, the analogous transfer from $\Gamma^{\mathrm{low}}_{\top}(N,q)$ along `conjLowerL`.
--
--   This is the classical $2\times 2$ composition table for the two degeneracy maps between level $N$ and level $Nq$ when $q$ already divides $N$: the diagonal entries are multiplication by $q$ and the off-diagonal entries are the Hecke operator $U_q$ and its transpose, which differ in this case. It is used in the construction of corner realisations in the local Hecke-algebra part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_iDeg_four_identities_of_dvd.lean

import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier in

theorem CohCarrier.jDeg_iDeg_four_identities_of_dvd (N q : ℕ) [NeZero N] [NeZero q]
    (A : Type) [AddCommGroup A] (hqN : q ∣ N)
    (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
    (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q) :
    (∀ φ, jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = q • φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = q • φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ q A hq' (iDeg' N (N * q) ⊤ ⊤ 1 A h1 φ) = heckeT N ⊤ q A φ) ∧
    (∀ φ, jDeg N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ) = heckeTlower N ⊤ q A φ) := by sorry
