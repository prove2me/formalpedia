-- Prove2me | Theorems.Thm_BCFGJPSSV26_Stable_costF_localSearch_le
-- name    : BCFGJPSSV26.Stable.costF_localSearch_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:46:20.298537+00:00
-- url     : https://prove2.me/theorems/e1e951b3-4050-491d-a271-916958eda395
-- title:
--   Corollary 1.5 (Part II) — the local search is a $(3+100/N)$-approximation
-- statement:
--   Part II (arXiv:2610.17172), Corollary 1.5, for the local search that the formalized algorithms run: with swaps of size $24N$, $N\ge201$, and a large enough budget, its output costs at most $(3+100/N)$ times the optimum.
--
--   **Setting.** Let $I$ be a valid $k$-median instance (clients and $m$ facilities with a rational pseudometric $d$, $k\ge1$, $m\ge1$) with $k\le m$, and let $|\mathrm{enc}(I)|$ be the length of its binary encoding. The cost of a set of facilities is the sum over the clients of the distance to the nearest facility of the set, and $\mathrm{opt}_k$ is the least cost of a nonempty set of at most $k$ facilities.
--
--   **The local search.** Given an integer $N$ and a budget $B$, the local search keeps a list of $k$ distinct facilities, initially the facilities $0,\dots,k-1$. A *swap* is a tuple of $24N$ numbers $x\lt km$, applied entry by entry: the facility at position $\lfloor x/m\rfloor$ of the list is replaced by the facility $x\bmod m$, unless the latter is already in the list. The swaps are enumerated in a fixed order, the tuples being built one coordinate at a time with at most $B$ of them kept at each stage (so all $(km)^{24N}$ are present when $B\ge(km)^{24N}$). One step applies the first enumerated swap whose result $T$ satisfies, in exact rational arithmetic, $\mathrm{cost}(T)<\bigl(1-\tfrac{1}{Nk}\bigr)\mathrm{cost}(S)$ for the current list $S$, and does nothing if there is none. The output is the list after $B$ steps.
--
--   **Statement.** Let $N\ge201$ and let $B$ be a natural number with $B\ge(km)^{24N}$ and $B\ge2Nk\,|\mathrm{enc}(I)|+2$. Then the set $S$ of facilities output by the local search with parameters $N$ and $B$ satisfies
--   $$\mathrm{cost}(S)\ \le\ \Bigl(3+\frac{100}{N}\Bigr)\,\mathrm{opt}_k .$$
--
--   In particular $\mathrm{cost}(S)\le4\,\mathrm{opt}_k$; this is the only property of the local search used in the bound on the number of unsynced clusters (Part II, Lemma 4.2), and it bounds the total sampling weight in the analyses of the client sampling and of the cluster sampling. With the fixed value $N=201$ and a budget polynomial in $|\mathrm{enc}(I)|$, the same local search also serves the main theorem of Part I for large $\varepsilon$.
--
--   **Formalization Note** Costs are computed exactly over the rationals. The two conditions on $B$ are those under which the output of the local search is an approximate local optimum for swaps of size $24N$ and threshold $1/(Nk)$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part II (arXiv:2610.17172), Corollary 1.5. Lean source: `BCFGJPSSV26.Stable.costF_localSearch_le`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/LocalSearch.lean#L598-L602

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Stable

open Tuples Encoding

variable {I : Instance}

theorem costF_localSearch_le (hv : I.Valid) (hk : I.k ≤ I.m) {N B : ℕ} (hN : 201 ≤ N)
    (hB₁ : (I.k * I.m) ^ Par.p N ≤ B) (hB₂ : 2 * N * I.k * (encInstance I).length + 2 ≤ B) :
    I.costF (I.centers (localSearch N (toRaw I) B)) ≤ (3 + 100 / N) * I.opt I.k := by sorry

end BCFGJPSSV26.Stable
end
