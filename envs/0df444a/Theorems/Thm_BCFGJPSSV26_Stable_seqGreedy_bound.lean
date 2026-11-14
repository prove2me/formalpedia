-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_seqGreedy_bound
-- name    : BCFGJPSSV26.Stable.seqGreedy_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:30.442361+00:00
-- url     : https://prove2.me/theorems/ce7ecb97-6bb1-45bd-8d42-3aa3bc06f9d6
-- title:
--   Sequential greedy guarantee: a $1-(T/(T+1))^T$ fraction with one element per part
-- statement:
--   This is the guarantee of the deterministic sequential greedy that the formalization uses for the submodular step of Part II, Section 5 (Lemma 5.1), in place of the continuous greedy: for a monotone submodular function and the constraint of one element from each of $\rho$ parts, the average value over the greedy lists is at least a $1-(T/(T+1))^T$ fraction of the value of any feasible choice.
--
--   Let $U$ be a set, $\rho\ge 0$ and $T\ge 1$ integers, and $f$ a real function on the finite subsets of $U$ that is monotone ($f(A)\le f(B)$ for $A\subseteq B$), submodular ($f(B\cup\{e\})-f(B)\le f(A\cup\{e\})-f(A)$ for $A\subseteq B$ and $e\in U$) and satisfies $f(\emptyset)=0$. Let $P_1,\dots,P_\rho$ be finite subsets of $U$ and let $L_j[t]\in U$, for $1\le j\le\rho$ and $1\le t\le T$, satisfy the *greedy rule*: $L_j[t]\in P_j$, and for every $e\in P_j$,
--
--   $$\sum_{V\in[T]^\rho}\Bigl(f\bigl(Q^{-j}_t(V)\cup\{e\}\bigr)-f\bigl(Q^{-j}_t(V)\bigr)\Bigr)\;\le\;\sum_{V\in[T]^\rho}\Bigl(f\bigl(Q^{-j}_t(V)\cup\{L_j[t]\}\bigr)-f\bigl(Q^{-j}_t(V)\bigr)\Bigr),$$
--
--   where $Q^{-j}_t(V)=\{L_{j'}[V_{j'}]:\ j'<j,\ V_{j'}\le t\}\cup\{L_{j'}[V_{j'}]:\ j'>j,\ V_{j'}<t\}$. Then for every choice of $o_j\in P_j$, $1\le j\le\rho$,
--
--   $$\Bigl(1-\bigl(\tfrac{T}{T+1}\bigr)^{T}\Bigr)\,f\bigl(\{o_1,\dots,o_\rho\}\bigr)\,T^{\rho}\;\le\;\sum_{V\in[T]^\rho}f\bigl(\{L_j[V_j]:\ 1\le j\le\rho\}\bigr).$$
--
--   In particular some $V$ gives a set $\{L_j[V_j]\}$ of value at least $(1-(T/(T+1))^T)\,f(\{o_j\})$, and $(T/(T+1))^T\le(1+1/T)/e$. The algorithm applies this with $T=N$ rounds to $f=g(\emptyset)-g$, the parts being the balls of the dummies and further copies of the set of all facilities for the guessed number of extra centers, and enumerates the sum over $[N]^\rho$, $\rho\le s$, within its time budget. This yields the greedy guarantee assumed in the bound on the submodular candidate (Theorem 3.4).
--
--   **Formalization Note** The parts need not be disjoint, and the sets $\{o_j\}$ and $\{L_j[V_j]\}$ are sets (repetitions collapse). Rounds and parts are indexed from $0$ in Lean.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Section 5 (used in place of the continuous greedy in Lemma 5.1). Lean source: `BCFGJPSSV26.Stable.seqGreedy_bound`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Submod/SeqGreedy.lean#L249-L290

module

public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Supermodular
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.Pi
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {U : Type*} [DecidableEq U] {ρ T : ℕ}

theorem seqGreedy_bound {f : Finset U → ℝ} (hmono : IsMonoF f) (hsub : IsSubmod f)
    (h0 : f ∅ = 0) (hT : 0 < T) {P : Fin ρ → Finset U} {Lst : Fin ρ → Fin T → U}
    (hG : IsSeqGreedy f P Lst) (o : Fin ρ → U) (ho : ∀ j, o j ∈ P j) :
    (1 - ((T : ℝ) / (T + 1)) ^ T) * f (univ.image o) * (T : ℝ) ^ ρ ≤
      ∑ V : Fin ρ → Fin T, f (univ.image fun j ↦ Lst j (V j)) := by sorry

end BCFGJPSSV26.Stable
end
