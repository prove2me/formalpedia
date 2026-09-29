-- Prove2me | Theorems.Thm_CohCarrier_threeCopy_injective_of_isEis
-- name    : CohCarrier.threeCopy_injective_of_isEis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9bb10f46-e7e0-5687-acbb-08458f2d4e69
-- title:
--   Injectivity of the localised three-copy degeneracy map
-- statement:
--   Let $R$ be a commutative ring, $A$ an $R$-module, $\ell_0$ a positive integer and $N,q$ positive integers. For each of the two steps $N \mid Nq$ and $Nq \mid Nq^2$ and each of the indices $1$ and $q$, assume the corresponding `LevelLE` data with full character groups: divisibility of levels, divisibility of the index into the quotient of levels, and compatibility of the unit groups. For a level $M$ write $H^1 =$ `H1 M ⊤ A`, the additive homomorphisms from $\mathrm{Additive}(\Gamma_H(M))$ to $A$, and let `Car R A M ⊤ ℓ₀` be this $R$-module regarded as an $R[X]$-module with $X$ acting by the Hecke operator `heckeTLin R A M ⊤ ℓ₀` at $\ell_0$. Let $rL, d$ be $R[X]$-linear maps from level $N$ to level $Nq$ and $i,j$ from level $Nq$ to level $Nq^2$, assumed to agree on the canonical images of classes with the degeneracy pullbacks `iDeg'` of index $1$ and of index $q$ respectively (for $rL,i$ the index $1$, for $d,j$ the index $q$). Let $gV$ and $gL2$ exhibit $R[X]$-modules $V'$ and $L2'$ as localisations of `Car R A N ⊤ ℓ₀` and `Car R A (N*q*q) ⊤ ℓ₀` at the powers of $\mathrm{tw} = X - (\ell_0+1)$. Assume: (i) whenever $g,h$ at level $N$ satisfy $\mathrm{iDeg}'_1 g + \mathrm{iDeg}'_q h = 0$ in level $Nq$, both $g$ and $h$ are Eisenstein, i.e. the Hecke operator at $\ell_0$ acts on them by $(\ell_0 : R) + 1$; (ii) whenever $x,z'$ at level $Nq$ satisfy $\mathrm{iDeg}'_1 x + \mathrm{iDeg}'_q z' = 0$ in level $Nq^2$, there is $w$ at level $N$ with $z' - \mathrm{iDeg}'_1 w$ and $x + \mathrm{iDeg}'_q w$ Eisenstein at level $Nq$. Then every $R[X]$-linear map $T' : V' \times V' \times V' \to L2'$ satisfying $T'(gV f_1, gV f_2, gV f_3) = gL2\bigl(i(rL f_1) + j(rL f_2) + j(d f_3)\bigr)$ for all triples $(f_1,f_2,f_3)$ of classes at level $N$ is injective.
--
--   This is the step, in the style of Wiles's use of Ihara's lemma, which converts control of the kernels of the pairs of degeneracy pullbacks in the tower $N \mid Nq \mid Nq^2$ — the kernels being Eisenstein for the Hecke operator at $\ell_0$, exactly where $X - (\ell_0+1)$ has been inverted — into injectivity of the three-copy degeneracy map after localisation. It is used by [`CohCarrier.injective_and_residual_of_isEis`](thm.html#CohCarrier.injective_and_residual_of_isEis).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_threeCopy_injective_of_isEis.lean

import Definitions.Def_CohCarrier_Tower
import Mathlib.Algebra.Module.LocalizedModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial

theorem CohCarrier.threeCopy_injective_of_isEis
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (rL d : Car R A N ⊤ ℓ₀ →ₗ[R[X]] Car R A (N * q) ⊤ ℓ₀)
    (i j : Car R A (N * q) ⊤ ℓ₀ →ₗ[R[X]] Car R A (N * q * q) ⊤ ℓ₀)
    (hrL : ∀ φ : H1 N ⊤ A, rL (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ))
    (hd : ∀ φ : H1 N ⊤ A, d (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ q A hq φ))
    (hi : ∀ ψ : H1 (N * q) ⊤ A, i (Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' ψ))
    (hj : ∀ ψ : H1 (N * q) ⊤ A, j (Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' ψ))
    {V' L2' : Type*} [AddCommGroup V'] [Module R[X] V'] [AddCommGroup L2'] [Module R[X] L2']
    (gV : Car R A N ⊤ ℓ₀ →ₗ[R[X]] V') [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gV]
    (gL2 : Car R A (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] L2') [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gL2]
    (hcore : ∀ g h : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 → IsEis R A N ⊤ ℓ₀ g ∧ IsEis R A N ⊤ ℓ₀ h)
    (h25 : ∀ x z' : H1 (N * q) ⊤ A,
      iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
        ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
          IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w))
    (T' : (V' × V' × V') →ₗ[R[X]] L2')
    (hT' : ∀ f : Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀,
      T' (gV f.1, gV f.2.1, gV f.2.2) = gL2 (threeCopy rL d i j f)) :
    Function.Injective T' := by sorry
