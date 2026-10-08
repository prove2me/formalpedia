-- Prove2me | Theorems.Thm_DiffVI_Conv_theorem_7_1
-- name    : DiffVI.Conv.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:32.568891+00:00
-- url     : https://prove2.me/theorems/607342b1-6d94-45d4-9b2b-05b9d719dd84
-- title:
--   Theorem 7.1, p. 44 — bounded time-stepping iterates have uniform / weak-L² limits along h_ν ↓ 0, and under (a) or (b) every limit is a weak solution of (6.2)
-- statement:
--   Throughout, $K\subseteq\mathbb R^m$ is a nonempty closed convex set, $T>0$, $\Omega=[0,T]\times\mathbb R^n$, and $f:\Omega\to\mathbb R^n$, $B:\Omega\to\mathbb R^{n\times m}$, $G:\Omega\to\mathbb R^m$ satisfy the standing assumptions (A) (Lipschitz continuity on $\Omega$) and (B) (boundedness of $B$ on $\Omega$); $F:\mathbb R^m\to\mathbb R^m$.
--
--   Fix $\theta\in[0,1]$ and $x^0\in\mathbb R^n$. For every integer $N\ge \bar N$ (where $\bar N\ge 1$), let $h=T/N$ and let $x^{h,0}=x^0,x^{h,1},\dots,x^{h,N}$ and $u^{h,1},\dots,u^{h,N}$ be iterates of the time-stepping scheme (7.2). Assume the uniform bounds (7.5): there are positive constants $c_{0,x},c_{1,x},c_{0,u},c_{1,u}$ with
--   $$\|x^{h,i+1}\|\le c_{0,x}+c_{1,x}\|x^0\|,\qquad \|u^{h,i+1}\|\le c_{0,u}+c_{1,u}\|x^0\|$$
--   for all such $h$ and all $i=0,\dots,N-1$.
--
--   Then:
--
--   1. There is a sequence $h_\nu=T/N_\nu\downarrow0$ (with $N_\nu\ge\bar N$ strictly increasing) along which the two limits exist: $\hat x^{h_\nu}\to\hat x$ uniformly on $[0,T]$ and $\hat u^{h_\nu}\rightharpoonup\hat u$ weakly in $L^2(0,T)$.
--   2. Suppose moreover one of the following:
--      - (a) $F(u)=\Psi(Eu)$ with $E\in\mathbb R^{\ell\times m}$ and $\Psi:\mathbb R^\ell\to\mathbb R^m$ Lipschitz continuous, and there is $c_{2,u}>0$ such that for all sufficiently small $h$, $\|Eu^{h,i+1}-Eu^{h,i}\|\le h\,c_{2,u}$ (7.6);
--      - (b) $F(u)=Du$ for a positive semidefinite matrix $D$.
--
--      Then every such limit pair $(\hat x,\hat u)$, along any strictly increasing sequence $N_\nu\ge\bar N$ for which both limits exist, is a weak solution of the initial-value DVI
--   $$\dot x=f(t,x)+B(t,x)u,\quad x(0)=x^0,\qquad u\in\mathrm{SOL}(K,G(t,x)+F).$$
--
--   This is the main convergence result for the time-stepping scheme (7.2): once the iterates are uniformly bounded, the scheme produces weak solutions of the DVI in the limit, which also proves existence of such solutions.
--
--   **Formalization Note** Step sizes are $h=T/N$ with $N=N_h+1\ge1$ an integer, so that the grid $t_{h,i}=ih$ ends exactly at $T$; "$h\in(0,\bar h]$" becomes "$N\ge\bar N$" and "$h_\nu\downarrow0$" a strictly increasing sequence of $N$'s. The iterates are hypotheses; the theorem does not construct them (Proposition 7.1 does). In (a), (7.6) is required for $1\le i\le N-1$, since the paper's convention $u^{h,0}\equiv u^{h,1}$ makes the case $i=0$ vacuous. A weak solution includes the integrability of both integrands (see the definition file).
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 44, Theorem 7.1, (7.5), (7.6)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Conv_Setting

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace DiffVI.Conv

local notation "𝔼" k:max => EuclideanSpace ℝ (Fin k)

open SolodovSvaiterVI.Alg21

/-- Theorem 7.1 (p. 44): under (7.5) the time-stepping interpolants have a uniform / weak-`L²`
limit along a subsequence `h_ν ↓ 0`; under (a) or (b), every such limit is a weak solution
of the initial-value DVI (6.2). -/
theorem theorem_7_1 {n m : ℕ} (K : Set (𝔼 m)) (hKne : K.Nonempty) (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    (T : ℝ) (hT : 0 < T) (f : ℝ → 𝔼 n → 𝔼 n) (B : ℝ → 𝔼 n → (𝔼 m →L[ℝ] 𝔼 n))
    (G : ℝ → 𝔼 n → 𝔼 m) (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B) (F : 𝔼 m → 𝔼 m)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (x0 : 𝔼 n) (xs : ℕ → ℕ → 𝔼 n) (us : ℕ → ℕ → 𝔼 m)
    (Nbar : ℕ) (hNbar : 1 ≤ Nbar)
    (hsch : ∀ N ≥ Nbar, IsScheme K f B G F T θ x0 N (xs N) (us N))
    (h75 : ∃ c0x c1x c0u c1u : ℝ, 0 < c0x ∧ 0 < c1x ∧ 0 < c0u ∧ 0 < c1u ∧
      ∀ N ≥ Nbar, ∀ i < N, ‖xs N (i + 1)‖ ≤ c0x + c1x * ‖x0‖ ∧
        ‖us N (i + 1)‖ ≤ c0u + c1u * ‖x0‖) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, Nbar ≤ φ k) ∧ ∃ (xl : ℝ → 𝔼 n) (ul : ℝ → 𝔼 m),
      TendstoUniformlyOn (fun k => xhat T (φ k) (xs (φ k))) xl atTop (Set.Icc (0 : ℝ) T) ∧
      WeakL2Tendsto T (fun k => uhat T (φ k) (us (φ k))) ul) ∧
    (((∃ (ℓ : ℕ) (E : 𝔼 m →L[ℝ] 𝔼 ℓ) (Ψ : 𝔼 ℓ → 𝔼 m) (LΨ : NNReal),
        (∀ u, F u = Ψ (E u)) ∧ LipschitzWith LΨ Ψ ∧
        ∃ c2u : ℝ, 0 < c2u ∧ ∃ N2 : ℕ, ∀ N ≥ N2, ∀ i : ℕ, 1 ≤ i → i < N →
          ‖E (us N (i + 1)) - E (us N i)‖ ≤ (T / N) * c2u) ∨
      (∃ D : 𝔼 m →L[ℝ] 𝔼 m, (∀ u, F u = D u) ∧ DiffVI.Exist.IsPSD D)) →
      ∀ (φ : ℕ → ℕ) (xl : ℝ → 𝔼 n) (ul : ℝ → 𝔼 m), StrictMono φ → (∀ k, Nbar ≤ φ k) →
        TendstoUniformlyOn (fun k => xhat T (φ k) (xs (φ k))) xl atTop (Set.Icc (0 : ℝ) T) →
        WeakL2Tendsto T (fun k => uhat T (φ k) (us (φ k))) ul →
        DiffVI.Exist.IsWeakSolution K f B G F T x0 xl ul) := by sorry

end DiffVI.Conv
