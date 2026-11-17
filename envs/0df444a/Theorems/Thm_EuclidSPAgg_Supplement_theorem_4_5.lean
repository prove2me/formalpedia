-- Prove2me | Theorems.Thm_EuclidSPAgg_Supplement_theorem_4_5
-- name    : EuclidSPAgg.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:45:25.956956+00:00
-- url     : https://prove2.me/theorems/0ce4f9be-3924-469a-ab0d-23daa44cd5ed
-- title:
--   Theorem 4.5 — a projective continuous median operation on a closed convex set is a coordinate-wise median
-- statement:
--   Let $C$ be a nonempty closed convex subset of a finite-dimensional Euclidean space $V$, and let $m:C^3\to C$ be a continuous median operation. For $a,b\in C$ write
--   $$
--   I(a,b)=\{m(a,b,z):z\in C\}
--   $$
--   for the median interval. Assume that every $I(a,b)$ is closed and Euclidean convex and that
--   $$
--   m(a,b,x)=P_{I(a,b)}\,x\qquad(a,b,x\in C), \tag{4.6}
--   $$
--   where $P_{I}$ is the Euclidean nearest-point projection onto $I$. Then there is one orthonormal basis $\mathcal B$ of the direction space of $\operatorname{aff}C$ such that
--   $$
--   m(a,b,c)=\mathrm{CM}_{\mathcal B}(a,b,c)\qquad(a,b,c\in C).
--   $$
--
--   The theorem straightens an abstract median structure in one orthonormal frame. Applied to the restriction of a symmetric strategyproof ternary rule to a core, it yields the coordinate-wise median formula of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Euclidean space → any finite-dimensional real inner product space $V$; reason: these are the same objects.
--   - encoding: "median operation" (not defined on the page; cited from Bowditch’s median algebras) → the median-algebra axioms symmetry, $m(a,a,b)=a$ and $m(a,b,m(c,d,e))=m(m(a,b,c),m(a,b,d),e)$ on $C$; reason: the standard definition, equivalent to the interval axioms the paper quotes.
--   - encoding: $m:C^3\to C$ continuous → a total ternary map sending $C^3$ into $C$, continuous on $C\times C\times C$ in the subspace topology; reason: only the values on $C^3$ are used.
--   - encoding: $m(a,b,x)=P_{I(a,b)}x$ → $\|x-m(a,b,x)\|\le\|x-y\|$ for every $y\in I(a,b)$; reason: $m(a,b,x)\in I(a,b)$ and the nearest point of a nonempty closed convex set is unique.
--   - encoding: $\mathrm{CM}_{\mathcal B}$ with an origin chosen in $\operatorname{aff}C$ → the identity holds for every origin $o\in C$; reason: the value does not depend on the origin in $\operatorname{aff}C$, so one origin and every origin give the same statement.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Theorem 4.5, display (4.6), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_EuclidSPAgg_Supplement_IsMedianOperation
import Definitions.Def_EuclidSPAgg_Supplement_frameMedian

namespace EuclidSPAgg.Supplement

/-- **Theorem 4.5** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.17 (PDF p.19)). Let `C` be a nonempty closed convex subset of a
finite-dimensional Euclidean space, and let `m : C³ → C` be a continuous median operation. For
`a, b ∈ C` write `I(a, b) = {m(a, b, z) : z ∈ C}`. Assume that every `I(a, b)` is closed and
Euclidean convex and that `m(a, b, x) = P_{I(a,b)} x` for `a, b, x ∈ C` (4.6). Then there is one
orthonormal basis `B` of the direction space of `aff C` such that `m(a, b, c) = CM_B(a, b, c)` for
all `a, b, c ∈ C`.

**Formalization Note** The ambient space is any finite-dimensional real inner product space `V`.
`m` is a total function whose values on `C³` are the operation; continuity is `ContinuousOn` of
the uncurried map on `C ×ˢ C ×ˢ C`, i.e. continuity in the subspace topology of `C³`. (4.6) says
that `m(a, b, x)` (which lies in `I(a, b)` since `x ∈ C`) is a nearest point of `I(a, b)` to `x`;
for a nonempty closed convex set the nearest point is unique, so this is `m(a, b, x) = P_{I(a,b)} x`.
The basis is indexed by `Fin r`, `r = dim (affineSpan ℝ C).direction`. `CM_B` is `frameMedian B o`
with origin `o ∈ C`; the conclusion is asserted for every origin `o ∈ C`, which is equivalent to one
origin since the value does not depend on `o ∈ aff C` (p.9). -/
theorem theorem_4_5 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (C : Set V) (hne : C.Nonempty) (hcl : IsClosed C)
    (hcv : Convex ℝ C) (m : V → V → V → V) (hm : IsMedianOperation C m)
    (hcont : ContinuousOn (fun p : V × V × V => m p.1 p.2.1 p.2.2) (C ×ˢ C ×ˢ C))
    (hI : ∀ a ∈ C, ∀ b ∈ C, IsClosed (m a b '' C) ∧ Convex ℝ (m a b '' C))
    (hproj : ∀ a ∈ C, ∀ b ∈ C, ∀ x ∈ C, ∀ y ∈ m a b '' C, ‖x - m a b x‖ ≤ ‖x - y‖) :
    ∃ B : OrthonormalBasis (Fin (Module.finrank ℝ (affineSpan ℝ C).direction)) ℝ
        (affineSpan ℝ C).direction,
      ∀ o ∈ C, ∀ a ∈ C, ∀ b ∈ C, ∀ c ∈ C, m a b c = frameMedian B o a b c := by sorry

end EuclidSPAgg.Supplement
