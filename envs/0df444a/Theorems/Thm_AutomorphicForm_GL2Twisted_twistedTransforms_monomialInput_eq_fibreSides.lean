-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides
-- name    : AutomorphicForm.GL2Twisted.twistedTransforms_monomialInput_eq_fibreSides
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/820060fe-71bc-5695-91ad-0f93f78963d2
-- title:
--   Twisted transforms of a monomial input equal fibre sides
-- statement:
--   Fix natural numbers $i,l$, a function $c \colon \mathbb{R} \to \mathbb{C}$ that is continuous and has compact support, and reals $a_1,a_2,r,\theta$ with $a_1>0$, $a_2>0$, $r>0$ and $0<\theta<\pi$. Consider the test function $\varphi$ on $\mathrm{GL}_2(\mathbb{C})$ given by $\varphi(g) = c(\mathrm{invFrobSq}\,g)\cdot \mathrm{monomialInput}\,i\,l\,g$, where `invFrobSq` $g = \mathrm{Re}\,\mathrm{tr}(g g^{*})$ is the squared Frobenius norm, and `monomialInput` is the product $\bigl((N-S+\Delta)/(2(N+2D))\bigr)^{i}\bigl((N-S-\Delta)/(2(N-2D))\bigr)^{l}$ with $N = \mathrm{invFrobSq}\,g$, $S = \mathrm{Re}\,\mathrm{tr}(g\cdot \bar g)$ for $\bar g$ the entrywise conjugate, $D = |\det g|$, and $\Delta = (\mathrm{invSecondRe}\,g - N S + 2D^{2})/D$ (the real quantity `invSecondRe`). The assertion is the conjunction of two identities. First, `twistedSplitTransform` $\varphi$ at $(a_1,a_2)$ — the integral over $v \in \mathbb{C}$ of the unitary average over $k$ of $\varphi(k^{-1}\,!![\sqrt{a_1},v;0,\sqrt{a_2}]\,\bar k)$ — equals $\int_{T>a_1+a_2} c(T)\cdot \tfrac12\,\mathrm{fibreMonomialFactor}\,i\,l\,T\,\sqrt{a_1a_2}\,(a_1+a_2)\cdot \mathrm{fibreArcIntegral}\,i\,l\,(2\pi)\,dT$. Second, `twistedEllipticTransform` $\varphi$ at $(r,\theta)$ — namely $4\sin^{2}\theta$ times $\int_{\rho>0}\int_{u\in\mathbb{C}} \rho^{-1}$ times the sum of the unitary averages of $\varphi$ along the twisted conjugates of the elliptic elements at parameters $(r,\theta,\rho,u)$ and $(r,-\theta,\rho,u)$ — equals $\int_{T>2r} c(T)\cdot (4\pi \sin\theta/r)\,\mathrm{fibreMonomialFactor}\,i\,l\,T\,r\,(2r\cos\theta)\cdot \mathrm{fibreArcIntegral}\,i\,l\,(\mathrm{ellipticArcLength}\,T\,r\,\theta)\,dT$.
--
--   This is the explicit evaluation of the twisted split and twisted elliptic orbital transforms at the complex place, for test functions of the form a radial profile in the squared Frobenius norm times a monomial in the two eigenvalue coordinates: both transforms become one-dimensional integrals of the profile against the corresponding fibre terms. It feeds the construction of test functions whose discrete-series pairing with both transforms vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_twistedTransforms_monomialInput_eq_fibreSides.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2TwistedMonomialFibres

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm.GL2Twisted

theorem
AutomorphicForm.GL2Twisted.twistedTransforms_monomialInput_eq_fibreSides
    (i l : ℕ) (c : ℝ → ℂ) (hc : Continuous c) (hcs : HasCompactSupport c) (a₁ a₂ r θ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hr : 0 < r) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi) :
    twistedSplitTransform (fun g : GL (Fin 2) ℂ => c (invFrobSq g) * ((monomialInput i l g : ℝ) : ℂ)) a₁ a₂ =
        splitFibreSide i l c a₁ a₂ ∧
    twistedEllipticTransform (fun g : GL (Fin 2) ℂ => c (invFrobSq g) * ((monomialInput i l g : ℝ) : ℂ)) r θ =
        ellipticFibreSide i l c r θ := by sorry
