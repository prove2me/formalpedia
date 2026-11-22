-- Prove2me | Theorems.Thm_AlpoGe_galoisLocalGlobalStrong_recParameter
-- name    : AlpoGe.galoisLocalGlobalStrong_recParameter
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-21T16:44:31.03421+00:00
-- url     : https://prove2.me/theorems/500eff66-60ee-4671-95d8-19d17c4a2c3a
-- title:
--   alpo.ge GRH release, Row0b: Galois representations for regular algebraic polarized cuspidal representations of GL_a over CM fields, with local–global compatibility
-- statement:
--   The proposition $\mathcal R$ = `UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)` of L. Alpöge's Lean proof of GRH (released 20 November 2026, written with Claude), which the release proves as `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`. With `AlpoGe.everyCharacter_of_row` ($\mathcal R$ implies the GRH half-plane statement) it gives the release's main theorem. All objects are the release's own definitions, published in the bundles `Def_AlpoGeB000`–`Def_AlpoGeB008`.
--
--   **Statement.** For every CM number field $E$, algebraic closure $\Omega$ of $E$, prime $\ell$, ring isomorphism $\iota:\overline{\mathbb Q}_\ell\cong\mathbb C$ and integer $a\ge1$, and for every cuspidal subrepresentation $\pi$ of $\mathrm{GL}_a$ over $E$ (in the space of smooth functions on $\mathrm{GL}_a(\mathbb A_E)$) and every Hecke character $\chi$ of the maximal totally real subfield $E^+$ such that $\pi$ is regular algebraic and $(\pi,\chi)$ is a polarized pair, there are a homomorphism $r:G_E\to\mathrm{GL}_a(\overline{\mathbb Q}_\ell)$, an integer $\mathrm{wt}$ and Hodge–Tate multisets $\mathrm{HT}(\tau)$ for the embeddings $\tau:E\to\overline{\mathbb Q}_\ell$ such that:
--
--   1. $r$ is continuous and semisimple;
--   2. **away from $\ell$:** at every finite place $w\nmid\ell$, for every place $A$ of $\Omega$ above $w$, every map $\mathrm{rc}$ from irreducible smooth representations of $\mathrm{GL}_n(E_w)$ to Weil–Deligne classes that satisfies the laws `IsRecT` (a local Artin map exists for which $\mathrm{rc}$ respects dimension, characters, Langlands data, cuspidality, twists by $|\cdot|^s$, absolute values of central characters, and, on "good" classes, twists, central characters, duals, injectivity, depth zero and a type law), and every local component $\sigma$ of $\pi$ at $w$, the Weil–Deligne class $x$ attached to $r$ at $A$ and $y=\mathrm{rc}(\text{normalized class of }\sigma)$ satisfy `AwayB`: $\dim x=\dim y$; $x=y$ when $y$ is monodromy-free and every commutator of the Weil group acts unipotently on $y$ ($\mathrm{Tor}$); and when $y$ is monodromy-free and satisfies $\mathrm{QpBig}$, $\mathrm{TmW}$ and $\mathrm{Sqf}$, $x$ is monodromy-free and has the same characteristic polynomials as $y$ on the degree-0 elements of the Weil group;
--   3. **weights:** $\mathrm{HT}(\tau)=\{\tfrac{a-1}2-z: z\in\mathrm{inf}_{\iota\circ\tau}(\pi)\}$ and $\mathrm{HT}(\tau\circ c)=\{\mathrm{wt}-n: n\in\mathrm{HT}(\tau)\}$;
--   4. **above $\ell$:** for every abstract system of period rings tied to concrete constructions of $A_{\inf}$, $B_{dR}$ and $B_{cris}$, and every local bridge identifying a decomposition group $D_A$ with $G_{K_w}$ for a finite extension $K_w/\mathbb Q_\ell$: at a spherical local component, $r|_{D_A}$ is crystalline and de Rham with Hodge–Tate jumps $\mathrm{HT}$; and whenever $y=\mathrm{rc}(\text{normalized local component})$ is monodromy-free and satisfies $\mathrm{QpBig}$, $\mathrm{TmW}$, $\mathrm{Sqf}$ or $\mathrm{Tor}$, $r|_{D_A}$ is de Rham and potentially semistable with jumps $\mathrm{HT}$, and its Weil–Deligne class (from $D_{pst}$, Frobenius-semisimplified) is `AwayB`-compatible with $y$.
--
--   **Formalization notes** (from a blind read-back of the Lean, not of any prose). Cuspidality of an automorphic form is the vanishing of its constant terms as Bochner integrals, which are $0$ when the integrand is not integrable, so the class of forms quantified over is at least the standard one. $\mathrm{TmW}$ reads characteristic polynomials of elements outside the Weil group as the junk value $1$. The above-$\ell$ clause is vacuous at places $w\nmid\ell$, since no local bridge induces such a place. The class attached to $r$ away from $\ell$ is a chosen class carrying Grothendieck's monodromy data for $r$ when one exists, and the trivial class of dimension $a$ otherwise; the class attached above $\ell$ is likewise trivial when $r|_{D_A}$ is not potentially semistable. Several objects are fixed by a choice (a degree witness, a Frobenius semisimplification, a representative of each isomorphism class, an infinitesimal character, with $\{0,\dots,0\}$ when none exists).
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc); the release's UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter, stated with its own definitions

import Mathlib
import Definitions.Def_AlpoGeB008

section

namespace AlpoGe

theorem galoisLocalGlobalStrong_recParameter :
    UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc := by
  sorry

end AlpoGe
end
