-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_4_5
-- name    : AbelianCayleyHDX.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:57.210955+00:00
-- url     : https://prove2.me/theorems/a8c5d3a5-4f80-4df2-ae3c-f70f8d7031d3
-- title:
--   Lemma 4.5 — maximal minors of a matrix of linear forms are affine along rank-one directions
-- statement:
--   Let $F$ be a field and $M(x) = (L_{ij}(x))_{1 \le i \le k,\ 1 \le j \le m}$ a matrix of linear forms on $V_0 = F^t$. Let $e \in V_0$ be a direction along which $M$ is an outer product: $L_{ij}(e) = a_i b_j$. Then for all $x \in V_0$ and $\alpha \in F$,
--   $$M(x + \alpha e) = M(x) + \alpha\, a b^{\mathsf T}, \qquad (4.2)$$
--   and for every $J \subseteq [m]$ with $|J| = k$ the maximal minor $p_J(x) = \det M_J(x)$ is affine in direction $[e]$. Consequently, if every direction of $D \subseteq \mathrm{PG}(t-1, F)$ has a representative $e$ of this kind, every $p_J$ belongs to $A(D)$.
--
--   In the paper, $x \in W^\vee \cong F^t$ for the Riemann–Roch space $W = L(G)$, $L_{ij}(x) = x(u_i z_j)$ for bases $u_i$ of $U \le L(A)$ and $z_j$ of $V \le L(B)$, and the directions are the evaluation functionals $e_P$ at the selected points, with $e_P(u_i z_j) = u_i(P) z_j(P)$; this is the instance $a = u(P)$, $b = z(P)$.
--
--   Differences from the source:
--   - generalization: the multiplication matrix $M(x) = (x(u_i z_j))$ on $W^\vee$ and the evaluation directions $e_P$ at the selected points $P$ → any $k \times m$ matrix of linear forms on $F^t$ and any direction $e$ with $L_{ij}(e) = a_i b_j$; reason: the proof uses only the rank-one identity; the paper's case is the instance $L_{ij}(x) = x(u_i z_j)$, $e = e_P$, $a = u(P)$, $b = z(P)$
--   - encoding: $M_J$, the square submatrix with column set $J$ → columns of $J$ taken in increasing order (`Finset.orderEmbOfFin`); reason: reordering columns only changes the sign of the minor
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 4.5, p.17, Eq. (4.2); setup of Section 4.2, p.16

import Mathlib
import Definitions.Def_AbelianCayleyHDX_affineSpace

namespace AbelianCayleyHDX

/-- **Lemma 4.5** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 4.5, p.17, Eq. (4.2), with the setup of Section 4.2, p.16), for a
general rank-one matrix of linear forms. Let `M(x) = (L_{ij}(x))` be a `k × m` matrix of linear
forms on `V₀ = F^t`, and let `e ∈ V₀` be a direction in which `M` is rank one:
`L_{ij}(e) = a_i b_j`. Then `M(x + αe) = M(x) + α a bᵀ` for all `x` and `α`, and for every
`J ⊆ [m]` with `|J| = k` the maximal minor `p_J(x) = det M_J(x)` is affine in direction `[e]`.
Consequently, if every direction of `D ⊆ PG(t − 1, F)` has such a representative, every `p_J`
belongs to `A(D)`.

**Formalization Note** In the paper `x ∈ W^∨ ≅ F^t`, `L_{ij}(x) = x(u_i z_j)`, the directions are
`[e_P]` for the selected points `P`, and `e_P(u_i z_j) = u_i(P) z_j(P)`, so `a = u(P)`, `b = z(P)`;
that is the instance of this statement. `M_J` takes the columns of `J` in increasing order. -/
theorem lemma_4_5 {F : Type*} [Field F] {t k m : ℕ} (L : Fin k → Fin m → Module.Dual F (Fin t → F)) :
    (∀ (e : Fin t → F) (a : Fin k → F) (b : Fin m → F), (∀ i j, L i j e = a i * b j) →
      (∀ (x : Fin t → F) (α : F), Matrix.of (fun i j => L i j (x + α • e)) =
        Matrix.of (fun i j => L i j x) + α • Matrix.vecMulVec a b) ∧
      ∀ (J : Finset (Fin m)) (hJ : J.card = k),
        IsAffineIn (fun x => (Matrix.of fun i l => L i (J.orderEmbOfFin hJ l) x).det) e) ∧
    ∀ D : Finset (PG t F),
      (∀ d ∈ D, ∃ (e : Fin t → F) (he : e ≠ 0) (a : Fin k → F) (b : Fin m → F),
        Projectivization.mk F e he = d ∧ ∀ i j, L i j e = a i * b j) →
      ∀ (J : Finset (Fin m)) (hJ : J.card = k),
        (fun x => (Matrix.of fun i l => L i (J.orderEmbOfFin hJ l) x).det) ∈ affineSpace D := by sorry

end AbelianCayleyHDX
