-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_31
-- name    : CubicPermFPRAS.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:46.428643+00:00
-- url     : https://prove2.me/theorems/d89198ec-6e07-42be-a64f-15246c6f395f
-- title:
--   Lemma 31, p.27 — the FAR flow bound: $\mathrm{En}_{\max}=O(\log n)$ and Eq. (24) (corrected: $\log(2n)$ for $\log n$)
-- statement:
--   There is a universal constant $C_0$ and, for every $\alpha>1$, a constant $C_\alpha$ such that the following holds. Let $\lambda$ be positive activities, $r$ an anchor, $w(r,\cdot)$ $\alpha$-rough anchor weights, $B$ the rescaled matrix, and $Z$ the normalizing constant of $\pi_B$. For every hole pattern $(u,v)$:
--
--   1. the coupling $\kappa_{u,v}$ admits a weighted routing family for the FAR chain in which every routing of positive weight has energy at most $C_0\log(2n)$;
--   2. for every $f:\Omega\to\mathbb R$,
--   $$\mathbb E_{(I,J)\sim\kappa_{u,v}}\big[(f(I)-f(J))^2\big]\le C_\alpha\,\frac{Z}{B(\mathcal N(u,v))}\,\log(2n)\,\mathcal E_{P_{\mathrm{FAR}}}(f,f).\tag{24}$$
--
--   This is the routing-energy flow bound behind the occupation estimate of Lemma 19.
--
--   Differences from the source:
--   - correction: $\mathrm{En}_{\max}=O(\log n)$ and the factor $\log n$ in (24) → $C_0\log(2n)$ and $\log(2n)$; reason: at $n=1$, $\Omega$ has two states and $\kappa_{u,v}$ puts mass $1$ on the pair (empty matching, the single edge), whose only routing has energy $1$, and (24) has a positive left side for $f$ separating the two states, while $\log 1=0$; for $n\ge2$, $\log(2n)\le2\log n$
--   - encoding: a weighted routing family with any finite label set → labels in $\Omega_{\mathrm{aux}}$; reason: the paper's labels are the perfect matchings, a subset of $\Omega_{\mathrm{aux}}$; existence with this label set implies existence in the source's sense
--   - encoding: $\mathrm{En}_{\max}=O(\log n)$ → a universal $C_0$ before $\alpha$, bounding the energy of every routing of positive weight; reason: $\mathrm{En}_{\max}$ is the maximum of these energies
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 31, p.27 (PDF 29); proof in §7

import Mathlib
import Definitions.Def_CubicPermFPRAS_farChain
import Definitions.Def_CubicPermFPRAS_routing
import Definitions.Def_mm_spectral

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 31** (flow bound for the FAR chain), p.27 (PDF 29), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…) (corrected: `log(2n)`
for `log n`); proved in §7.

For positive activities `λ`, an anchor `r`, `α`-rough anchor weights and the FAR chain built
from `B`, with `Z` the normalizing constant of `π_B`: for every hole pattern `(u,v)` the coupling
`κ_{u,v}` admits a weighted routing family with `En_max = O(log n)`, and for every
`f : Ω → ℝ`, `E_{(I,J)∼κ_{u,v}}[(f(I) − f(J))²] ≤ C_α (Z/B(N(u,v))) log n · E_{P_FAR}(f,f)` (24).

**Formalization Note.** The family's labels are taken in `Ω_aux` (the paper's labels are the
perfect matchings, a subset). `En_max ≤ C log(2n)` says every routing occurrence of positive
weight has energy at most `C log(2n)`. Both bounds are stated with `log(2n)`: at `n = 1` the
printed `log n` is `0`, while `κ_{u,v}` puts mass `1` on a pair at distance one (energy `1`, and a
positive left side of (24) for `f` separating the two states of `Ω`). For `n ≥ 2`,
`log(2n) ≤ 2 log n`. `E_{P_FAR}` is `MarkovMixing.dirichletForm` with respect to `π_B`. -/
theorem lemma_31 : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ α : ℝ, 1 < α → ∃ Cα : ℝ, 0 < Cα ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w → ∀ u v : Fin n,
      (∃ F : WeightedRoutingFamily (farP (Bmat lam w)) (kappa lam u v) (Asg n),
        ∀ I a J, 0 < F.khat I a J → energy (F.route I a J) ≤ C₀ * Real.log (2 * n)) ∧
      ∀ f : Omega n → ℝ,
        ∑ I, ∑ J, kappa lam u v I J * (f I - f J) ^ 2 ≤
          Cα * (farZ (Bmat lam w) / familyWeight (Bmat lam w) (NSet u v)) * Real.log (2 * n) *
            MarkovMixing.dirichletForm (farP (Bmat lam w)) (piB (Bmat lam w)) f := by sorry

end CubicPermFPRAS
