-- Prove2me | Theorems.Thm_CohCarrier_injective_and_residual_of_isEis
-- name    : CohCarrier.injective_and_residual_of_isEis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/5a195b94-523e-5864-ba76-be8c24cfa694
-- title:
--   Injectivity and varpi-divisibility for the localised level-raising map
-- statement:
--   Fix a commutative ring $R$, $R$-modules $A$ and $B$, naturals $\ell_0, q \neq 0$ and $N$, and level inclusions $h_1, h_q$ from $N$ to $Nq$ and $h_1', h_q'$ from $Nq$ to $Nq^2$ (each `LevelLE` asserting the divisibility of levels, divisibility of the quotient by $1$ resp. $q$, and compatibility of the full unit subgroups). Let $\varpi \in R$ and $g : A \to B$ be $R$-linear with $\ker g \subseteq \varpi A$, with $\varpi$ acting injectively on $A$ and annihilating $B$. For each of $A$ and $B$ one is given $R[X]$-linear maps $rL, d$ on the modules $\mathrm{Car} = H^1(\Gamma_{\top}(\cdot), \cdot)$, i.e. additive homomorphisms from $\Gamma_H$ into the coefficients with $X$ acting by the Hecke operator `heckeTLin` at $\ell_0$, from level $N$ to level $Nq$, and $i, j$ from $Nq$ to $Nq^2$, which on classes are the degeneracy maps `iDeg'` attached to $h_1, h_q, h_1', h_q'$; also coefficient-change maps $cV$ at level $N$ and $cL$ at level $Nq^2$ given by post-composition with $g$. Two Eisenstein hypotheses are assumed over each of $A$ and $B$: if $\mathrm{iDeg}'_1 u + \mathrm{iDeg}'_q v = 0$ at level $Nq$ then $u$ and $v$ satisfy $T_{\ell_0} = \ell_0 + 1$, and if $\mathrm{iDeg}'_1 x + \mathrm{iDeg}'_q z' = 0$ at level $Nq^2$ then some $w$ at level $N$ makes $z' - \mathrm{iDeg}'_1 w$ and $x + \mathrm{iDeg}'_q w$ Eisenstein at level $Nq$. Finally $gVA, gLA, gVB, gLB$ are localisation maps of the four relevant modules at the powers of $X - C(\ell_0 + 1)$, with targets $VA, LA, VB, LB$; $TA$ and $TB$ are maps $V^3 \to L$ compatible via these with $(x,y,z) \mapsto i(rL\,x) + j(rL\,y) + j(d\,z)$ over $A$ resp. $B$; $rV$ and $rL2$ are compatible with $cV$ and $cL$; and $TqV$ is an arbitrary endomorphism of $VA$. The conclusion is that $v \mapsto TA(qv, -TqV\,v, v)$ is injective on $VA$, and that whenever $TA(qv, -TqV\,v, v) = C\varpi \cdot x$ for some $x \in LA$, then $v \in C\varpi \cdot VA$.
--
--   This is the injectivity and residual-injectivity input to the level-raising argument in the style of Ihara's lemma: over the localisation at the Eisenstein-free part of the Hecke algebra, the three-copy degeneracy combination composed with $v \mapsto (qv, -T v, v)$ is injective, and injective modulo $\varpi$ in the divisibility sense. It is used by [`CohCarrier.injective_and_residual_cornerSubmodule_of_isEis`](thm.html#CohCarrier.injective_and_residual_cornerSubmodule_of_isEis), which transfers the statement to the relevant corner submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_injective_and_residual_of_isEis.lean

import Definitions.Def_CohCarrier_Tower
import Mathlib.Algebra.Module.LocalizedModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial

theorem CohCarrier.injective_and_residual_of_isEis
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (B : Type) [AddCommGroup B] [Module R B]
    (ϖ : R) (g : A →ₗ[R] B) (hker : ∀ a, g a = 0 → ∃ a₁, a = ϖ • a₁)
    (hreg : ∀ a : A, ϖ • a = 0 → a = 0) (hB : ∀ b : B, ϖ • b = 0)
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
    (rLB dB : Car R B N ⊤ ℓ₀ →ₗ[R[X]] Car R B (N * q) ⊤ ℓ₀)
    (iB jB : Car R B (N * q) ⊤ ℓ₀ →ₗ[R[X]] Car R B (N * q * q) ⊤ ℓ₀)
    (hrLB : ∀ φ : H1 N ⊤ B, rLB (Module.AEval'.of (heckeTLin R B N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ 1 B h₁ φ))
    (hdB : ∀ φ : H1 N ⊤ B, dB (Module.AEval'.of (heckeTLin R B N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ q B hq φ))
    (hiB : ∀ ψ : H1 (N * q) ⊤ B, iB (Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R B (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 B h₁' ψ))
    (hjB : ∀ ψ : H1 (N * q) ⊤ B, jB (Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R B (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ q B hq' ψ))
    (cV : Car R A N ⊤ ℓ₀ →ₗ[R[X]] Car R B N ⊤ ℓ₀)
    (hcV : ∀ φ : H1 N ⊤ A, cV (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B N ⊤ ℓ₀) (g.toAddMonoidHom.comp φ))
    (cL : Car R A (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] Car R B (N * q * q) ⊤ ℓ₀)
    (hcL : ∀ ψ : H1 (N * q * q) ⊤ A, cL (Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R B (N * q * q) ⊤ ℓ₀) (g.toAddMonoidHom.comp ψ))
    {VA LA VB LB : Type*} [AddCommGroup VA] [Module R[X] VA] [AddCommGroup LA] [Module R[X] LA]
    [AddCommGroup VB] [Module R[X] VB] [AddCommGroup LB] [Module R[X] LB]
    (gVA : Car R A N ⊤ ℓ₀ →ₗ[R[X]] VA) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gVA]
    (gLA : Car R A (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] LA) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gLA]
    (gVB : Car R B N ⊤ ℓ₀ →ₗ[R[X]] VB) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gVB]
    (gLB : Car R B (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] LB) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gLB]
    (hcoreA : ∀ g h : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 → IsEis R A N ⊤ ℓ₀ g ∧ IsEis R A N ⊤ ℓ₀ h)
    (h25A : ∀ x z' : H1 (N * q) ⊤ A,
      iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
        ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
          IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w))
    (hcoreB : ∀ g h : H1 N ⊤ B,
      iDeg' N (N * q) ⊤ ⊤ 1 B h₁ g + iDeg' N (N * q) ⊤ ⊤ q B hq h = 0 → IsEis R B N ⊤ ℓ₀ g ∧ IsEis R B N ⊤ ℓ₀ h)
    (h25B : ∀ x z' : H1 (N * q) ⊤ B,
      iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 B h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q B hq' z' = 0 →
        ∃ w : H1 N ⊤ B, IsEis R B (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 B h₁ w) ∧
          IsEis R B (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q B hq w))
    (TA : (VA × VA × VA) →ₗ[R[X]] LA)
    (hTA : ∀ f : Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀,
      TA (gVA f.1, gVA f.2.1, gVA f.2.2) = gLA (threeCopy rL d i j f))
    (TB : (VB × VB × VB) →ₗ[R[X]] LB)
    (hTB : ∀ f : Car R B N ⊤ ℓ₀ × Car R B N ⊤ ℓ₀ × Car R B N ⊤ ℓ₀,
      TB (gVB f.1, gVB f.2.1, gVB f.2.2) = gLB (threeCopy rLB dB iB jB f))
    (rV : VA →ₗ[R[X]] VB) (hrV : ∀ v, rV (gVA v) = gVB (cV v))
    (rL2 : LA →ₗ[R[X]] LB) (hrL2 : ∀ x, rL2 (gLA x) = gLB (cL x))
    (TqV : VA →ₗ[R[X]] VA) :
    Function.Injective (TA ∘ₗ embComb (q : R[X]) TqV) ∧
      ∀ (v : VA) (x : LA), TA (embComb (q : R[X]) TqV v) = (C ϖ : R[X]) • x →
        ∃ v₁ : VA, v = (C ϖ : R[X]) • v₁ := by sorry
