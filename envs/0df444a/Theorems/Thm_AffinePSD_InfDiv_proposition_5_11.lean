-- Prove2me | Theorems.Thm_AffinePSD_InfDiv_proposition_5_11
-- name    : AffinePSD.InfDiv.proposition_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:48.193886+00:00
-- url     : https://prove2.me/theorems/12432ff9-2ec8-44ac-b939-16528eaa6ad1
-- title:
--   Proposition 5.11 — for $\alpha=0$ the Riccati solutions $(\varphi(t,\cdot),\psi(t,\cdot))$ lie in $(\mathcal C,\mathcal C^S)$
-- statement:
--   Let $(\alpha=0,b,\beta^{ij},c,\gamma,m,\mu)$ be an admissible parameter set, with $F$ and $R$ as in (2.16)–(2.17). Let $(\varphi,\psi)$ be the solutions of the generalized Riccati equations
--   $$\partial_t\varphi(t,u)=F(\psi(t,u)),\ \varphi(0,u)=0,\qquad\partial_t\psi(t,u)=R(\psi(t,u)),\ \psi(0,u)=u,\qquad u\in S_d^+.$$
--   Then for all $t\ge0$,
--   $$\varphi(t,\cdot)\in\mathcal C\qquad\text{and}\qquad\psi(t,\cdot)\in\mathcal C^S.$$
--
--   So without a diffusion part, $e^{-\varphi(t,u)-\langle\psi(t,u),x\rangle}$ is the Laplace transform of an infinitely divisible sub-stochastic kernel. This gives (ii) $\Rightarrow$ (iii) in Theorem 2.9.
--
--   **Formalization Note** "The solutions" are taken to be the $S_d^+$-valued solutions of (2.14)–(2.15), $u\in S_d^+$, that are jointly continuous on $\mathbb R_+\times S_d^+$, as the exponents of an affine process are (Lemma 3.2(iii)). For $u\in S_d^{++}$ the solution is unique, and joint continuity determines the values for $u\in\partial S_d^+$. $\varphi$ and $\psi$ are functions on $\mathbb R\times M_d$, evaluated at $t\ge0$ and positive semidefinite $u$.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §5.3, Proposition 5.11, p. 51

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone
import Definitions.Def_AffinePSD_Necessity_Params
import Definitions.Def_AffinePSD_Necessity_Process
import Definitions.Def_AffinePSD_InfDiv_LevyKhintchine

namespace AffinePSD.InfDiv

/-- Proposition 5.11 (arXiv:0910.0137v3, §5.3, p. 51). Let `(α = 0, b, β^{ij}, c, γ, m, μ)` be an
admissible parameter set. Then for all `t ≥ 0`, the solutions `(φ(t,·), ψ(t,·))` of (2.14) and
(2.15) lie in `(C, C^S)`.
Formalization Note: "the solutions" are the `S_d^+`-valued solutions of (2.14)–(2.15), for
`u ∈ S_d^+`, that are jointly continuous on `ℝ_+ × S_d^+` (as the exponents of an affine process are,
Lemma 3.2(iii)); for `u ∈ S_d^{++}` the solution is unique, and joint continuity pins down the
values on `∂S_d^+`. `φ, ψ` live on `ℝ × AffinePSD.Necessity.Mat d` and are evaluated at `t ≥ 0`, `u` AffinePSD.Necessity.PSD. -/
theorem proposition_5_11 {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) (hP : AffinePSD.Necessity.Admissible χ P)
    (hα : P.α = 0) (φ : ℝ → AffinePSD.Necessity.Mat d → ℝ) (ψ : ℝ → AffinePSD.Necessity.Mat d → AffinePSD.Necessity.Mat d)
    (hR : AffinePSD.Necessity.SolvesRiccati (AffinePSD.Necessity.Fpar P) (AffinePSD.Necessity.Rpar χ P) φ ψ)
    (hφc : ContinuousOn (fun q : ℝ × AffinePSD.Necessity.Mat d => φ q.1 q.2) (Set.Ici 0 ×ˢ {u | AffinePSD.Necessity.PSD u}))
    (hψc : ContinuousOn (fun q : ℝ × AffinePSD.Necessity.Mat d => ψ q.1 q.2) (Set.Ici 0 ×ˢ {u | AffinePSD.Necessity.PSD u})) :
    ∀ t, 0 ≤ t → (fun u => φ t u) ∈ CC d ∧ (fun u => ψ t u) ∈ CS d := by sorry

end AffinePSD.InfDiv
