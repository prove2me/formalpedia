-- Prove2me | Theorems.Thm_EuclidKSteiner_corollary_4_7
-- name    : EuclidKSteiner.corollary_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:18:41.30075+00:00
-- url     : https://prove2.me/theorems/149c4177-db9b-43fc-b6c5-48eb947c6289
-- title:
--   Corollary 4.7 — the compressed recurrence represents $D[u,i,v]$
-- statement:
--   Work in the graph setting, with $\Phi$ taken with respect to $M$ and the ground set $P$. Fix a template $T$ with $r$ terminal roles in total, a vertex $u$, its child $u_i$ and a host $v$. Suppose $\widehat D[u,i-1,v]$ represents $D[u,i-1,v]$ and, for every host $v'$, $\widehat D[u_i,\mathrm{child}(u_i),v']$ represents $D[u_i,\mathrm{child}(u_i),v']$ (each as a family of sets of the size given by the number of terminal roles of its partial template, with completed size $r$). Then
--   $$\widetilde D[u,i,v]=\bigcup_{\substack{v'\ne v\\ v'\text{ fits }u_i}}\{(A\cup A',w+w'+w_{uu_i}(v,v')):(A,w)\in\widehat D[u,i-1,v],\,(A',w')\in\widehat D[u_i,\mathrm{child}(u_i),v'],\,A\cap A'=\emptyset\}$$
--   represents $D[u,i,v]$.
--
--   The dynamic program may therefore compress every entry by Theorem 3.8 without losing an optimal solution.
--
--   **Formalization Note** Children are indexed from $0$: the child at position $i$ of the list of children is the page's $u_{i+1}$, and the statement relates the entries with $i$ and $i+1$.
--
--   Differences from the source:
--   - generalization: a fixed augmented tree template (Definition 4.2) → every well-formed code, without conditions 1–4 of Definition 4.2; reason: the argument uses none of those conditions; templates are well-formed codes
--   - encoding: children u_1, …, u_child(u) and the entry D[u, i, v] → the child at 0-based position i and the entries D[u, i, v], D[u, i+1, v]; reason: 0-based indexing
--   - encoding: representative subfamily for Φ with every compression using the same total r → Representative S.Phi S.P r p with r the number of terminal roles of the whole template and p that of the partial template; reason: §4.2, p.17: 'Every compression uses this same total r'
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Corollary 4.7, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_EuclidKSteiner_Representative
import Definitions.Def_EuclidKSteiner_Template

namespace EuclidKSteiner

/-- **Corollary 4.7 (Representative-family recurrence).** Bhore, Kisfaludi-Bak, Marx, Odak,
*Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256
75361687…), Corollary 4.7, p.19 (PDF p.21): "Suppose the input families are representative
subfamilies of their corresponding full table entries. Then the family D̃[u, i, v] = … represents
D[u, i, v]."

Let `T` be a well-formed template with `r` terminal roles in total, `u` a vertex, `u_i = c` its
`i`-th child (`1 ≤ i ≤ child(u)`), and `v` a host. If `D̂₁` represents `D[u, i − 1, v]` and, for every
host `v'`, `D̂₂(v')` represents `D[c, child(c), v']` (for `Φ` with respect to `M`, ground set `P`,
completed size `r`, and the numbers of terminal roles of the partial templates as set sizes), then
the family `D̃[u, i, v]` obtained by the transition (4.4) from `D̂₁` and `D̂₂` represents `D[u, i, v]`.

**Formalization Note** The child index is 0-based: `(children u)[i] = c` is the page's `u_{i+1}`, and
the statement relates `D[u, i, v]`, `D[c, child(c), ·]` to `D[u, i + 1, v]`. "Every compression uses
this same total r" (p.17): `r` is the number of terminal roles of the whole template. Stated for every
well-formed code (Definition 4.2's conditions are not used). -/
theorem corollary_4_7 {V : Type*} [Fintype V] [DecidableEq V] (S : GraphSetting V) (T : Template)
    (hT : T.WellFormed) (u : ℕ) (hu : u < T.size) (i c : ℕ) (hc : (T.children u)[i]? = some c)
    (v : V) (D₁ : Set (Finset V × ℝ)) (D₂ : V → Set (Finset V × ℝ))
    (h₁ : Representative S.Phi S.P T.numTerminals (T.termCount (T.partialVerts u i))
      (S.Dfull T u i v) D₁)
    (h₂ : ∀ v' : V, Representative S.Phi S.P T.numTerminals
      (T.termCount (T.partialVerts c (T.nch c))) (S.Dfull T c (T.nch c) v') (D₂ v')) :
    Representative S.Phi S.P T.numTerminals (T.termCount (T.partialVerts u (i + 1)))
      (S.Dfull T u (i + 1) v) (S.transition T c D₁ D₂ v) := by sorry

end EuclidKSteiner
