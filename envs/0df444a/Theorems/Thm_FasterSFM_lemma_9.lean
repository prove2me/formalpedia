-- Prove2me | Theorems.Thm_FasterSFM_lemma_9
-- name    : FasterSFM.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:52.786412+00:00
-- url     : https://prove2.me/theorems/584b6402-2dd1-4d82-9ba9-7213f407e48a
-- title:
--   Lemma 9 — one self-concordant barrier on every section
-- statement:
--   Let $P$ be a cutting-plane body with its $2n$ cube rows and inserted rows with $\|v_i\|_2\le1$ and $\rho_i>0$; let $M$ be its number of rows, $W=n+\lambda M$ and $c=400/\lambda$. For $x\in\operatorname{int}P$ and a direction $u$, put $\eta_i=-v_i^\top u/s_i$, $\|u\|_x^2=u^\top H_{\mathrm{fl}}(x)u=\sum_i\eta_i^2$ and $Q=\sum_i\ell_i(x)\eta_i^2$. Then
--
--   $$Q+\lambda\|u\|_x^2\le D^2\Psi_{\mathrm{fl}}[u,u]\le3Q+\lambda\|u\|_x^2\le(3+\lambda)\|u\|_x^2,$$
--   $$|D^3\Psi_{\mathrm{fl}}[u,u,u]|\le\frac{40}{\sqrt\lambda}\,(D^2\Psi_{\mathrm{fl}}[u,u])^{3/2},\qquad |D\Psi_{\mathrm{fl}}[u]|^2\le W\,D^2\Psi_{\mathrm{fl}}[u,u].$$
--
--   Moreover, for every linear subspace $S$ with orthonormal basis $J$, on the relative interior $\Omega=\{y: s_i(Jy)>0\ \forall i\}$ of the section $P_S$:
--
--   1. $c\Psi_S$ is a standard self-concordant function: three times continuously differentiable and convex on $\Omega$, with $|D^3(c\Psi_S)[w]|\le2(D^2(c\Psi_S)[w])^{3/2}$, and $\Psi_S\to+\infty$ at the relative boundary;
--   2. $\lambda H_S\preceq\nabla^2\Psi_S\preceq(3+\lambda)H_S$;
--   3. $\Psi_{\mathrm{fl}}$ has a unique minimizer on $P_S$, attained in its relative interior.
--
--   The lemma makes the single full-space barrier usable on every section reached after contractions, with constants independent of the number of rows.
--
--   Differences from the source:
--   - generalization: inserted offsets ρ_i ≥ δ → inserted offsets ρ_i > 0; reason: the proof uses only positivity of the offsets; bodies of the algorithm satisfy it
--   - encoding: x ∈ int P and u ∈ S, for every linear subspace S → every u ∈ ℝⁿ; reason: every vector lies in some subspace, so the two quantifications agree
--   - encoding: a linear subspace S (basis J) → the column space of a matrix J ∈ ℝ^{n×N} with JᵀJ = I; reason: every subspace has an orthonormal basis; same instances
--   - encoding: D^kΨ_fl[u,…,u] → the k-th derivative of t ↦ Ψ_fl(x + tu) at 0; reason: definition of the directional derivative
--   - encoding: cΨ_S standard self-concordant on the relative interior of P_S [NT08, Def. 2.1] → C³ and convex on Ω, |D³| ≤ 2(D²)^{3/2} on Ω, and Ψ_S(y_k) → +∞ for every sequence in Ω converging to a point outside Ω; reason: the definition of §2.2, p.4, spelled out
--   - encoding: λH_S ⪯ ∇²Ψ_S ⪯ (3+λ)H_S → the inequalities of the quadratic forms at every y ∈ Ω, with ∇²Ψ_S the Hessian matrix; reason: Loewner order as quadratic forms
--   - encoding: a unique minimizer on P_S attained in its relative interior → a unique y ∈ Ω minimizing Ψ_S over Ω; reason: Ψ_fl is +∞ on the relative boundary in the paper; Lean's log 0 = 0 is a junk value there
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Lemma 9, p.19

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Barrier

namespace FasterSFM

open Classical Matrix Filter Topology

/-- **Lemma 9** (One barrier on every section), p.19.

Ene & Nguyen, arXiv:2610.25403v1, Lemma 9, p.19.

"Let c = 400/λ and W = n + λM. For every linear subspace S the restriction cΨ_S is a standard
self-concordant function on the relative interior of P_S. More precisely, fix x ∈ int P and a direction
u ∈ S, and let η_i = −v_iᵀu/s_i, ‖u‖²_x = uᵀH_fl(x)u = Σ_i η_i², Q = Σ_i ℓ_i(x)η_i². Then
Q + λ‖u‖²_x ≤ D²Ψ_fl[u,u] ≤ 3Q + λ‖u‖²_x ≤ (3+λ)‖u‖²_x,
|D³Ψ_fl[u,u,u]| ≤ (40/√λ)(D²Ψ_fl[u,u])^{3/2},
|DΨ_fl[u]|² ≤ W D²Ψ_fl[u,u].
In particular λH_S ⪯ ∇²Ψ_S ⪯ (3+λ)H_S, and Ψ_fl has a unique minimizer on every section P_S,
attained in its relative interior."

The body has the `2n` cube rows and any inserted rows with `‖v_i‖₂ ≤ 1` and `ρ_i > 0`; `M = 2n + k`.

**Formalization Note.**
* Generalization: inserted offsets need only be positive (the paper's bodies have `ρ_i ≥ δ`).
* Since `S` ranges over all subspaces, `u ∈ S` ranges over all of `ℝⁿ`. `D^kΨ_fl[u,…,u]` is the `k`-th
  derivative of `t ↦ Ψ_fl(x + tu)` at `0`.
* A subspace `S` of dimension `N` is the column space of `J` with `JᵀJ = I`; the relative interior of
  `P_S` in the coordinates `y` (`x = Jy`) is `Ω = {y : s_i(Jy) > 0 ∀ i}` (rows with `Jᵀv_i = 0` have
  constant slack `ρ_i > 0` on `S`).
* "Standard self-concordant on Ω" ([NT08, Def. 2.1], §2.2 p.4) is spelled out: `cΨ_S` is `C³` and
  convex on the open set `Ω`, `|D³(cΨ_S)[w]| ≤ 2(D²(cΨ_S)[w])^{3/2}` on `Ω`, and `Ψ_S(y_k) → +∞`
  whenever `y_k ∈ Ω` converge to a point outside `Ω`.
* `λH_S ⪯ ∇²Ψ_S ⪯ (3+λ)H_S` is stated for the quadratic forms on `Ω`, with `∇²Ψ_S` the Hessian
  matrix of `Ψ_S`.
* "Unique minimizer on P_S attained in its relative interior": a unique `y ∈ Ω` minimizing `Ψ_S` over
  `Ω` (on the relative boundary the paper's `Ψ_fl` is `+∞`). -/
theorem lemma_9 {n : ℕ} (P : Body n)
    (hP : ∀ i : Fin P.k, (∑ j, P.v i j ^ 2) ≤ 1 ∧ 0 < P.ρ i) :
    (∀ x : Fin n → ℝ, P.Interior x → ∀ u : Fin n → ℝ,
      let η : Row n P.k → ℝ := fun i => -(P.rowV i ⬝ᵥ u) / P.slack i x
      let nx : ℝ := u ⬝ᵥ (P.Hfl x *ᵥ u)
      let Q : ℝ := ∑ i, P.lev x i * η i ^ 2
      let D2 : ℝ := dirDeriv 2 P.Psi x u
      nx = ∑ i, η i ^ 2 ∧
      Q + lam * nx ≤ D2 ∧ D2 ≤ 3 * Q + lam * nx ∧ 3 * Q + lam * nx ≤ (3 + lam) * nx ∧
      |dirDeriv 3 P.Psi x u| ≤ 40 / Real.sqrt lam * D2 ^ ((3 : ℝ) / 2) ∧
      (dirDeriv 1 P.Psi x u) ^ 2 ≤ P.W * D2) ∧
    (∀ (N : ℕ) (J : Matrix (Fin n) (Fin N) ℝ), Jᵀ * J = 1 →
      let Ω : Set (Fin N → ℝ) := {y | P.Interior (J *ᵥ y)}
      let f : (Fin N → ℝ) → ℝ := fun y => cSC * P.PsiS J y
      IsOpen Ω ∧ ContDiffOn ℝ 3 f Ω ∧ ConvexOn ℝ Ω f ∧
      (∀ y ∈ Ω, ∀ w : Fin N → ℝ,
        |dirDeriv 3 f y w| ≤ 2 * (dirDeriv 2 f y w) ^ ((3 : ℝ) / 2)) ∧
      (∀ (ys : ℕ → Fin N → ℝ) (yb : Fin N → ℝ), (∀ j, ys j ∈ Ω) →
        Tendsto ys atTop (𝓝 yb) → yb ∉ Ω → Tendsto (fun j => P.PsiS J (ys j)) atTop atTop) ∧
      (∀ y ∈ Ω, ∀ w : Fin N → ℝ,
        lam * (w ⬝ᵥ (P.HS J y *ᵥ w)) ≤ w ⬝ᵥ (hess (P.PsiS J) y *ᵥ w) ∧
        w ⬝ᵥ (hess (P.PsiS J) y *ᵥ w) ≤ (3 + lam) * (w ⬝ᵥ (P.HS J y *ᵥ w))) ∧
      ∃! y, y ∈ Ω ∧ ∀ y' ∈ Ω, P.PsiS J y ≤ P.PsiS J y') := by sorry

end FasterSFM
