-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_taylor_remainder
-- name    : DiffNeighbors.Bias.taylor_remainder
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T08:41:22.750278+00:00
-- url     : https://prove2.me/theorems/fab36078-c09c-4e9d-9fc9-3c899ae2ff94
-- title:
--   Proof of Theorem 1, §3.3, p. 11 (corrected: factor ½) — the first-order approximation's error is ½(a − p)ᵀH^a(p′)(a − p)
-- statement:
--   Let $h : \{0,1\}^N \to \mathbb R$ with multilinear extension $F$, let $a \in \{0,1\}$ and $p \in \mathbb R$, and write $\mathbf a = (a, \dots, a)$ and $\mathbf p = (p, \dots, p)$. Let $H(w)$ be the Hessian of $F$ at $w$; by the second-partial identity its entries are $H_{jk}(w) = \mathbb E_w[\Delta_{jk} h(Z)]$ for $j \neq k$ and $H_{jj}(w) = 0$. Then there is a point $p' = (s, \dots, s)$ on the segment from $\mathbf p$ to $\mathbf a$ (that is, $s$ between $p$ and $a$) such that the error of the first-order approximation of $F(\mathbf a)$ around $\mathbf p$ is
--   $$F(\mathbf a) - \Bigl(F(\mathbf p) + \sum_j (a - p)\frac{\partial F}{\partial w_j}(\mathbf p)\Bigr) = \frac12 (\mathbf a - \mathbf p)^\top H(p')(\mathbf a - \mathbf p) = \frac12 \sum_j \sum_{k \neq j} (a - p)^2\, \mathbb E_{p'}[\Delta_{jk} h(Z)].$$
--
--   Applied to $h = f^a_i$, this is the error of the DN estimator's first-order approximation to $F^a_i(a)$, which Theorem 1's proof then bounds by $\tfrac12 d^2 \epsilon$ for each treatment.
--
--   The page states the error as $(a - p)^\top H^a(p')(a - p)$ without the factor $\frac12$; that is the Lagrange form of Taylor's theorem with the $\frac12$ dropped, and it is false (see below). With the $\frac12$ restored, the two errors for $a = 1$ and $a = 0$ add up to at most $d^2\epsilon$, which is Theorem 1's bound.
--
--   **Formalization Note** $\partial F/\partial w_j(\mathbf p)$ is written as $\mathbb E_{\mathbf p}[h \mid Z_j = 1] - \mathbb E_{\mathbf p}[h \mid Z_j = 0]$ (the first-partial identity), and the Hessian through its entries as above; `Set.uIcc p (ind a)` is the closed interval between $p$ and $a$.
--
--   Differences from the source:
--   - correction: the error is (a − p)ᵀH^a(p′)(a − p) → the error is ½(a − p)ᵀH^a(p′)(a − p); reason: the printed form is false: a node with two neighbours and f¹(z) = z₁z₂ (1-smooth, satisfies Assumption 1), a = 1, p = ½ gives F¹(w) = w₁w₂, H ≡ [[0,1],[1,0]], error 1 − (¼ + ½(½ + ½)) = ¼, while (a − p)ᵀH(p′)(a − p) = ½ for every p′; the Lagrange remainder carries ½
--   - reading: there exists some p′ → p′ = (s, …, s) with s in the closed interval between p and a; reason: p′ is the intermediate point of Taylor's theorem on the segment from (p,…,p) to (a,…,a); an unrestricted p′ would leave the subsequent bound without content
--   - encoding: H^a(p′) and (a − p)ᵀ∇F^a(p) → Σ_j Σ_{k≠j} (a − p)² mlExt (secondDiff h j k) (s,…,s), and Σ_j (a − p)(E_p[h|Z_j=1] − E_p[h|Z_j=0]); reason: the Hessian entries and the gradient as identified by the second- and first-partial identities
--   - generalization: F^a of node i, p ∈ (0,1), a sum over N_i → the multilinear extension of any h : {0,1}^ι → ℝ, any real p, sums over all coordinates; reason: specializes with h = condOutcome f i a, whose partial derivatives in coordinates outside N_i vanish under Assumption 1
--   - encoding: units [N] = {1,…,N}, treatment vectors z ∈ {0,1}^N, an undirected graph without self-loops, d = max_i |N_i| → a finite type ι with N = card ι, z : ι → Bool with 1/0 read through ind, G : SimpleGraph ι, N_i = G.neighborFinset i, d = G.maxDegree; reason: a simple graph is exactly an undirected graph without self-loops; same instances
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 11, §3.3 (proof of Theorem 1), 'There exists some p′ such that the error of the DN estimator's first-order approximation to F^a(a) is (a − p)^⊤ H^a(p′)(a − p).'

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Model

namespace DiffNeighbors.Bias

open Finset

/-- **Taylor remainder of the first-order approximation** (corrected: factor `½`), §3.3, p. 11.
For `a ∈ {0, 1}` there is a point `p′ = (s, …, s)` on the segment from `(p, …, p)` to `(a, …, a)` with
`F(a) − [F(p) + (a − p)ᵀ∇F(p)] = ½ (a − p)ᵀ H(p′) (a − p)`,
where the Hessian `H(p′)` has entries `E_{p′}[Δ_jk h(Z)]` off the diagonal and `0` on it. -/
theorem taylor_remainder {ι : Type*} [Fintype ι] [DecidableEq ι] (h : (ι → Bool) → ℝ) (a : Bool)
    (p : ℝ) :
    ∃ s ∈ Set.uIcc p (ind a),
      mlExt h (fun _ => ind a) - mlExt h (fun _ => p)
        - ∑ j, (ind a - p) * (mlExt (fun z => h (Function.update z j true)) (fun _ => p)
            - mlExt (fun z => h (Function.update z j false)) (fun _ => p))
      = (1 / 2) * ∑ j, ∑ k ∈ Finset.univ.erase j,
          (ind a - p) ^ 2 * mlExt (fun z => secondDiff h j k z) (fun _ => s) := by sorry

end DiffNeighbors.Bias
