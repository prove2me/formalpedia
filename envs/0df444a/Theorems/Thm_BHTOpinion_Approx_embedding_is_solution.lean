-- Prove2me | Theorems.Thm_BHTOpinion_Approx_embedding_is_solution
-- name    : BHTOpinion.Approx.embedding_is_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:59.254995+00:00
-- url     : https://prove2.me/theorems/4b0843ba-a085-4442-97e6-5ed1e45a3439
-- title:
--   Section 4 — t ↦ G(ξ(t/n)) solves the continuum equation (3.2) from G(ξ(0)) (time rescaled by 1/n; see Formalization Note)
-- statement:
--   Let $n\ge1$ and let $\xi:[0,\infty)\to\mathbb R^n$ be a solution of the discrete-agent integral equation (2.1). Let $G$ be the embedding of $\mathbb R^n$ into step functions on $I=[0,1]$, $G(\xi)(\alpha)=\xi_i$ for $\alpha\in[\frac{i-1}n,\frac in)$ and $G(\xi)(1)=\xi_n$. Then
--
--   $$x_t(\alpha)=G\bigl(\xi(t/n)\bigr)(\alpha),\qquad t\ge0,\ \alpha\in I,$$
--
--   is a solution of the continuum-agent integral equation (3.2) with initial condition $G(\xi(0))$.
--
--   The $n$-agent model is thus a special case of the continuum model, run on a slower clock: each block of agents in the continuum has mass $1/n$, so the continuum interaction felt by a block is $1/n$ times the discrete one. This is what links Proposition 4 to the $n$-agent model in Theorem 7.
--
--   **Formalization Note** The page writes "$G(\xi(t))$ is a solution to (3.2) with $G(\xi(0))$ as initial condition". As printed this is false: for $\alpha$ in block $i$, $\mathcal L(G(\xi))(\alpha)=\frac1n\sum_{j:|\xi_i-\xi_j|<1}(\xi_j-\xi_i)$, which is $\frac1n$ times the right-hand side of (2.1). The statement is therefore made with time rescaled, $G(\xi(t/n))$. Equivalently, $G(\xi(t))$ solves (3.2) when $\xi$ solves the weighted model (2.4) with all weights $w_j=1/n$ (p. 5220); only the rescaled form is formalized. Sortedness of $\xi$ and properness are not needed.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), Section 4, pp. 5231–5232, the sentence 'One can verify that G(ξ(t)) is a solution to the continuum-agent integral equation (3.2) with G(ξ(0)) as initial condition' (time rescaled; see note)

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Discrete
import Definitions.Def_BHTOpinion_Approx_Continuum

namespace BHTOpinion.Approx

theorem embedding_is_solution (n : ℕ) (hn : 0 < n) (ξ : ℝ → Fin n → ℝ)
    (hξ : IsDiscreteSolution ξ) :
    BHTOpinion.Continuum.IsSolution (G (ξ 0)) (fun t α => G (ξ (t / n)) α) := by sorry

end BHTOpinion.Approx
