-- Prove2me | Theorems.Thm_AbelianCayleyHDX_theorem_1_2
-- name    : AbelianCayleyHDX.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:08.398585+00:00
-- url     : https://prove2.me/theorems/4bfea42c-ec09-485b-b9b7-5a3756f6e234
-- title:
--   Theorem 1.2 — explicit 2D Cayley complexes over $\mathbb F_2^n$ with $\lambda$-expanding vertex links and Cayley degree $n^{O(\log(2+1/\lambda))}$
-- statement:
--   For every fixed $\lambda > 0$ there is an explicit infinite family of two-dimensional Cayley complexes over $\mathbb F_2^n$, with $n \to \infty$ along the family. Each complex is simple, pure, unweighted and translation invariant. Its one-skeleton and vertex links are connected, the random-walk operator of every vertex link has all nontrivial eigenvalues in $[-\lambda, \lambda]$, its Cayley degree is $n^{O(\log(2+1/\lambda))}$, and every edge lies in $O_\lambda(\log n)$ triangles.
--
--   Precisely: there is an absolute constant $C > 0$ such that for every $\lambda > 0$ there are $C_\lambda > 0$ and a family $(n_j, S_j, T_j)_{j \ge 0}$ with $n_j \to \infty$ such that for every $j$:
--   1. $T_j$ (with the uniform distribution) is a translation-invariant two-dimensional Cayley complex over $\mathbb F_2^{n_j}$ with generators $S_j$;
--   2. $\mathrm{Cay}(\mathbb F_2^{n_j}, S_j)$ is connected;
--   3. every vertex link is connected and a two-sided $\lambda$-spectral expander;
--   4. $|S_j| \le n_j^{\,C\log(2+1/\lambda)}$;
--   5. every edge lies in at most $C_\lambda \log n_j$ triangles;
--
--   and the family is explicit in the sense of Section 2.3 (one machine outputs member $j$ in time polynomial in $n_j$).
--
--   This answers the two-dimensional case of the question of Dikstein, Liu and Wigderson (Question 1.1) with polynomial Cayley degree.
--
--   Differences from the source:
--   - reading: Cayley degree $n^{O(\log(2+1/\lambda))}$ → $|S_j| \le n_j^{C\log(2+1/\lambda)}$ with one constant $C$ chosen before $\lambda$; reason: the $O$ has no subscript; with $C$ depending on $\lambda$ the clause would only say $n^{O_\lambda(1)}$
--   - reading: every edge lies in $O_\lambda(\log n)$ triangles → at most $C_\lambda \log n_j$ triangles, $C_\lambda$ chosen after $\lambda$, for every member $j$; reason: the bound is uniform over the family; members have $n_j \ge 2$ in the paper's construction
--   - reading: the random-walk operator of every vertex link has all nontrivial eigenvalues in $[-\lambda, \lambda]$; vertex links are connected → every vertex link is a two-sided $\lambda$-spectral expander (connected and $\|P|_{\mathbf 1^{\perp_\pi}}\|_\pi \le \lambda$, Section 2.2); reason: $P$ is $\pi$-self-adjoint, so the norm on $\mathbf 1^{\perp_\pi}$ is the largest absolute nontrivial eigenvalue
--   - reading: explicit infinite family → a sequence indexed by $j \in \mathbb N$ with $n_j \to \infty$ and one Turing machine and polynomial $p$ outputting member $j$ (from $j$ in binary) within $p(n_j)$ steps, per the definition on p.9; reason: p.9 defines explicitness; a deterministic algorithm is modelled by a multi-stack Turing machine
--   - encoding: simple, pure, unweighted complex → a `Finset` of 3-sets with the uniform distribution; reason: a `Finset` holds each face once; uniform = unweighted
--   - encoding: the group $\mathbb F_2^n$ → `Fin n → ZMod 2`; reason: Lean convention; same group
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Theorem 1.2, p.4

import Mathlib
import Definitions.Def_AbelianCayleyHDX_cayleyGraph
import Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
import Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_HasLocalSpectralNorm
import Definitions.Def_AbelianCayleyHDX_IsExplicitFamily
import Definitions.Def_ReplParity_Vec
open Filter
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Theorem 1.2** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Theorem 1.2, p.4). For every fixed `λ > 0` there is an explicit
infinite family of two-dimensional Cayley complexes over `𝔽₂ⁿ`, with `n → ∞` along the family.
Each complex is simple, pure, unweighted and translation invariant. Its one-skeleton and vertex
links are connected, the random-walk operator of every vertex link has all nontrivial eigenvalues
in `[−λ, λ]`, its Cayley degree is `n^{O(log(2 + 1/λ))}`, and every edge lies in `O_λ(log n)`
triangles.

Stated as: there is an absolute constant `C > 0` such that for every `λ > 0` there are `C_λ > 0`
and a sequence `(n_j, S_j, T_j)` with `n_j → ∞`, where for every `j`, `T_j` (the triangles, with
the uniform distribution) is a translation-invariant two-dimensional Cayley complex over `𝔽₂^{n_j}`
with generators `S_j`, `Cay(𝔽₂^{n_j}, S_j)` is connected, every vertex link is connected and a
two-sided `λ`-spectral expander (Section 2.2), `|S_j| ≤ n_j^{C log(2 + 1/λ)}`, and every edge lies in
at most `C_λ log n_j` triangles; and the family is explicit (Section 2.3, p.9).

**Formalization Note** `C` is chosen before `λ` (an `O(·)` in the exponent with a constant
depending on `λ` would only say `n^{O_λ(1)}`). The spectral clause is Section 2.2's
`‖P|_{1^⊥π}‖_π ≤ λ` on each link, equivalent to "all nontrivial eigenvalues in `[−λ, λ]`" since `P`
is `π`-self-adjoint. Simple holds by the `Finset` encoding; unweighted means uniform on `T_j`. The
bounds hold for every member, not only eventually. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ Cl : ℝ, 0 < Cl ∧
      ∃ (n : ℕ → ℕ) (S : ∀ j, Finset (Vec (n j))) (T : ∀ j, Finset (Finset (Vec (n j)))),
        Tendsto n atTop atTop ∧
        (∀ j, IsCayleyComplex (S j) (T j) ∧ IsTranslationInvariant (T j) ∧
          (cayleyGraph (S j)).Connected ∧ HasLocalSpectralNorm (T j) lam ∧
          ((S j).card : ℝ) ≤ (n j : ℝ) ^ (C * Real.log (2 + 1 / lam)) ∧
          ∀ e ∈ edges (T j), (triCount (T j) e : ℝ) ≤ Cl * Real.log (n j)) ∧
        IsExplicitFamily n S T := by sorry

end AbelianCayleyHDX
